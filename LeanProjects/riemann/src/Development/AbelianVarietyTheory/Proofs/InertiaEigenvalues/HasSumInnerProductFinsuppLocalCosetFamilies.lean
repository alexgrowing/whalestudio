import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TrivialLevelCosetRepresentativeMemLevel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open Classical

noncomputable section

namespace GlobalTheory.RawLift.FamSum

section Generic

theorem map_listProd {Γ ι : Type} [Group Γ] (c : Γ →* Γ) (v : ι) (r : ι → Γ) (h1 : c (r v) = r v)
    (h0 : ∀ w, w ≠ v → c (r w) = 1) (l : List ι) (hl : l.Nodup) :
    c (l.map r).prod = if v ∈ l then r v else 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.prod_cons, map_mul, ih hl.2]
    by_cases ha : a = v
    · subst ha
      simp [hl.1, h1]
    · simp [h0 a ha, Ne.symm ha]

theorem mul_listProd {Γ ι : Type} [Group Γ] (φ : Γ → ℂ) (h1 : φ 1 = 1) (r : ι → Γ) (S : ι → Subgroup Γ)
    (hS : ∀ v w, w ≠ v → r w ∈ S v) (hφ : ∀ v, ∀ γ ∈ S v, φ (γ * r v) = φ γ * φ (r v)) (l : List ι) (hl : l.Nodup) :
    φ (l.map r).prod = (l.map fun w => φ (r w)).prod := by
  induction l using List.reverseRecOn with
  | nil => simpa using h1
  | append_singleton l a ih =>
    rw [List.nodup_append] at hl
    simp only [List.map_append, List.prod_append, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [hφ a, ih hl.1]
    refine (S a).list_prod_mem fun x hx => ?_
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
    exact hS a w (hl.2.2 w hw a (List.mem_singleton_self a))

end Generic

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem isFinIdem_fid (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : IsFinIdem D v (Eu.fid D v) := by
  have h : ∃ f, IsFinIdem D v f := by
    obtain ⟨ε, hε⟩ := GlobalTheory.IdemSupport.exists_placeIdem (D := D) v
    exact ⟨_, ε, hε, rfl⟩
  unfold Eu.fid
  rw [dif_pos h]
  exact h.choose_spec

theorem fid_orth {v w : HeightOneSpectrum (𝓞 D.host.F)} (h : v ≠ w) : Eu.fid D v * Eu.fid D w = 0 := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨ε, hε, e⟩ := isFinIdem_fid D v
  obtain ⟨ε', hε', e'⟩ := isFinIdem_fid D w
  rw [e, e']
  exact GlobalTheory.IdemSupport.place_orth hΦ hε hε' h

theorem mem_GfC_of_fid (V : HSp D) {v : HeightOneSpectrum (𝓞 D.host.F)} {g : GA D V} (h : SuppF V (Eu.fid D v) g) :
    g ∈ GfC V := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  obtain ⟨ε, hε, e⟩ := isFinIdem_fid D v
  rw [e] at h
  exact GlobalTheory.IdemSupport.mem_GfC_of_suppF V (GlobalTheory.IdemSupport.place_comp hΦ hε).1 h

theorem trivAt_iff (V : HSp D) (f : Formalism.L2.Theta.AE D) (g : GA D V) :
    TrivAt V f g ↔ g ∈ GlobalTheory.IdemSupport.suppGroup V (1 - f) := by
  change _ ↔ SuppF V (1 - f) g
  refine forall_congr' fun i => forall_congr' fun j => ?_
  constructor <;> intro h <;> linear_combination -h

theorem eq_one_of_supp_triv (V : HSp D) {f : Formalism.L2.Theta.AE D} {g : GA D V} (h : SuppF V f g) (h' : TrivAt V f g) :
    g = 1 := by
  apply GlobalTheory.IdemSupport.mt_inj V
  rw [GlobalTheory.IdemSupport.mt_one, ← sub_eq_zero]
  ext a b
  rw [← h a b, h' a b]
  rfl

theorem trivAt_of_supp (V : HSp D) {f f' : Formalism.L2.Theta.AE D} (hf : f * f' = 0) {g : GA D V} (h : SuppF V f' g) :
    TrivAt V f g := by
  intro a b
  rw [← h a b, ← mul_assoc, hf, zero_mul]

theorem cmp_self (V : HSp D) {f : Formalism.L2.Theta.AE D} {g c : GA D V} (hg : SuppF V f g) (hc : SuppF V f c)
    (ht : TrivAt V f (g * c⁻¹)) : c = g := by
  have : g * c⁻¹ ∈ GlobalTheory.IdemSupport.suppGroup V f := mul_mem hg (inv_mem (show c ∈ _ from hc))
  have h := eq_one_of_supp_triv V this ht
  exact (mul_inv_eq_one.1 h).symm

theorem cmp_other (V : HSp D) {f : Formalism.L2.Theta.AE D} {g c : GA D V} (hg : TrivAt V f g) (hc : SuppF V f c)
    (ht : TrivAt V f (g * c⁻¹)) : c = 1 := by
  refine eq_one_of_supp_triv V hc ?_
  rw [trivAt_iff] at hg ht ⊢
  have := mul_mem (inv_mem ht) hg
  simpa using this

theorem rep_supp {R : RealDat D A Ks} {i : Fin D.R.m} {v : HeightOneSpectrum (𝓞 D.host.F)} (x : Eu.LX R i v) :
    Eu.rep x ∈ GfC (Wc D i) ∧ SuppF (Wc D i) (Eu.fid D v) (Eu.rep x) := (Quotient.out x).2

theorem eq_of_rep {R : RealDat D A Ks} {i : Fin D.R.m} {v : HeightOneSpectrum (𝓞 D.host.F)} {x y : Eu.LX R i v}
    (h : (Eu.rep x)⁻¹ * Eu.rep y ∈ levW R i) : x = y := by
  rw [← Quotient.out_eq x, ← Quotient.out_eq y]
  apply Quotient.sound
  change ((QuotientGroup.leftRel (levW R i)).comap _) _ _
  rw [Setoid.comap_rel, QuotientGroup.leftRel_apply]
  exact h

theorem rep_mk {R : RealDat D A Ks} {i : Fin D.R.m} {v : HeightOneSpectrum (𝓞 D.host.F)} (g : Eu.locSet R i v) :
    (Eu.rep (R := R) (i := i) (v := v) (Quotient.mk _ g))⁻¹ * g.1 ∈ levW R i := by
  have h := Quotient.mk_out (s := (QuotientGroup.leftRel (levW R i)).comap
    (Subtype.val : Eu.locSet R i v → GA D (Wc D i))) g
  rw [Setoid.comap_rel, QuotientGroup.leftRel_apply] at h
  exact h

theorem famProd_mem (R : RealDat D A Ks) (i : Fin D.R.m) (F : ∀ v, Eu.LX R i v) : Eu.famProd R i F ∈ GfC (Wc D i) := by
  unfold Eu.famProd
  split_ifs with h
  · refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx
    exact (rep_supp (F w)).1
  · exact one_mem _

theorem cmp_famProd (R : RealDat D A Ks) (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.host.F))
    (c : GA D (Wc D i) →* GA D (Wc D i))
    (hc : ∀ g, SuppF (Wc D i) (Eu.fid D v) (c g) ∧ TrivAt (Wc D i) (Eu.fid D v) (g * (c g)⁻¹))
    (F : ∀ v, Eu.LX R i v) (hF : {w | F w ≠ Eu.lx0 R i w}.Finite) :
    (c (Eu.famProd R i F))⁻¹ * Eu.rep (F v) ∈ levW R i := by
  unfold Eu.famProd
  rw [dif_pos hF, map_listProd c v (fun w => Eu.rep (F w)) (cmp_self _ (rep_supp (F v)).2 (hc _).1 (hc _).2)
    (fun w hw => cmp_other _ (trivAt_of_supp _ (fid_orth hw.symm) (rep_supp (F w)).2) (hc _).1 (hc _).2) _
    (Finset.nodup_toList _)]
  split_ifs with h
  · rw [inv_mul_cancel]; exact one_mem _
  · have : F v = Eu.lx0 R i v := by
      by_contra hne
      exact h (Finset.mem_toList.2 (hF.mem_toFinset.2 hne))
    rw [inv_one, one_mul, this]
    exact Eu.trivial_level_coset_representative_mem_level R i v

def famCls (R : RealDat D A Ks) (i : Fin D.R.m) (F : {F : ∀ v, Eu.LX R i v // {w | F w ≠ Eu.lx0 R i w}.Finite}) :
    GfC (Wc D i) ⧸ (levW R i).subgroupOf (GfC (Wc D i)) :=
  QuotientGroup.mk ⟨Eu.famProd R i F.1, famProd_mem R i F.1⟩

theorem famCls_bijective (R : RealDat D A Ks) (i : Fin D.R.m) (h : LevProd R i) : Function.Bijective (famCls R i) := by
  obtain ⟨-, -, cmp, h1, h2⟩ := h
  have hc := fun v => cmp_famProd R i v (cmp v) (h1 v _ (isFinIdem_fid D v))
  constructor
  · intro F F' e
    have e1 : (Eu.famProd R i F.1)⁻¹ * Eu.famProd R i F'.1 ∈ levW R i :=
      Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.1 e)
    have e2 := (h2 _ (mul_mem (inv_mem (famProd_mem R i F.1)) (famProd_mem R i F'.1))).1.1 e1
    refine Subtype.ext (funext fun v => eq_of_rep ?_)
    have e3 := e2 v
    rw [map_mul, map_inv] at e3
    have := mul_mem (mul_mem (inv_mem (hc v F.1 F.2)) e3) (hc v F'.1 F'.2)
    simpa only [_root_.mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel_left] using this
  · intro q
    obtain ⟨⟨g, hg⟩, rfl⟩ := QuotientGroup.mk_surjective q
    have hm : ∀ v, cmp v g ∈ Eu.locSet R i v := fun v =>
      ⟨mem_GfC_of_fid _ (h1 v _ (isFinIdem_fid D v) g).1, (h1 v _ (isFinIdem_fid D v) g).1⟩
    let F : ∀ v, Eu.LX R i v := fun v => Quotient.mk _ ⟨cmp v g, hm v⟩
    have hr : ∀ v, (Eu.rep (F v))⁻¹ * cmp v g ∈ levW R i := fun v => rep_mk ⟨cmp v g, hm v⟩
    have hF : {w | F w ≠ Eu.lx0 R i w}.Finite := by
      refine (h2 g hg).2.subset fun w hw hk => hw (eq_of_rep ?_)
      have := mul_mem (mul_mem (hr w) (inv_mem hk)) (Eu.trivial_level_coset_representative_mem_level R i w)
      simpa only [mul_assoc, mul_inv_cancel_left] using this
    refine ⟨⟨F, hF⟩, QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 ?_)⟩
    change (Eu.famProd R i F)⁻¹ * g ∈ levW R i
    refine (h2 _ (mul_mem (inv_mem (famProd_mem R i F)) hg)).1.2 fun v => ?_
    rw [map_mul, map_inv]
    have := mul_mem (hc v F hF) (hr v)
    simpa only [mul_assoc, mul_inv_cancel_left] using this

theorem out_famCls (R : RealDat D A Ks) (i : Fin D.R.m)
    (F : {F : ∀ v, Eu.LX R i v // {w | F w ≠ Eu.lx0 R i w}.Finite}) :
    ∃ k ∈ levW R i, ((famCls R i F).out : GfC (Wc D i)) = Eu.famProd R i F.1 * k := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul ((levW R i).subgroupOf (GfC (Wc D i)))
    ⟨Eu.famProd R i F.1, famProd_mem R i F.1⟩
  exact ⟨k.1.1, Subgroup.mem_subgroupOf.1 k.2, congrArg Subtype.val hk⟩

theorem coef_famProd (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (hM : FinMult R i t) (hLF : LevFix R i t)
    (hVN : VecNe R i t) {μ 𝓕} (hμ : IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕)
    (F : ∀ v, Eu.LX R i v) (hF : {w | F w ≠ Eu.lx0 R i w}.Finite) :
    coef R i t μ 𝓕 (Eu.famProd R i F) = ∏ᶠ v, Eu.acoef R i t μ 𝓕 v (F v) := by
  rw [finprod_eq_prod_of_mulSupport_subset (s := hF.toFinset), ← Finset.prod_map_toList]
  · unfold Eu.famProd
    rw [dif_pos hF]
    refine mul_listProd (coef R i t μ 𝓕) (Model.coef_one R i t hVN μ 𝓕 hμ) (fun w => Eu.rep (F w))
      (fun v => GfC (Wc D i) ⊓ GlobalTheory.IdemSupport.suppGroup (Wc D i) (1 - Eu.fid D v)) (fun v w hw => ?_)
      (fun v γ hγ => ?_) _ (Finset.nodup_toList _)
    · exact ⟨(rep_supp (F w)).1, (trivAt_iff _ _ _).1 (trivAt_of_supp _ (fid_orth hw.symm) (rep_supp (F w)).2)⟩
    · exact hM μ 𝓕 hμ v _ (isFinIdem_fid D v) γ hγ.1 ((trivAt_iff _ _ _).2 hγ.2) _ (rep_supp (F v)).2
  · intro v hv
    rw [Finset.mem_coe, Set.Finite.mem_toFinset]
    intro e
    apply hv
    change Eu.acoef R i t μ 𝓕 v (F v) = 1
    rw [e]
    exact Eu.local_coefficient_trivial_level_coset hLF hVN hμ v

theorem trPair_eq_bop {R : RealDat D A Ks} {i : Fin D.R.m} (h : TransLaws R i) {γ : GA D (Wc D i)}
    (hγ : γ ∈ GfC (Wc D i)) (x y) : trPair R i γ x y = ⟪x, Eu.Bop R i γ y⟫_ℂ := by
  have hex := h.2.2.1 γ hγ
  unfold Eu.Bop
  rw [dif_pos hex]
  exact hex.choose_spec.2 x y

theorem coef_out (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) (hM : FinMult R i t) (hLF : LevFix R i t)
    (hVN : VecNe R i t) {μ 𝓕} (hμ : IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕)
    (F : {F : ∀ v, Eu.LX R i v // {w | F w ≠ Eu.lx0 R i w}.Finite}) :
    coef R i t μ 𝓕 ((famCls R i F).out : GfC (Wc D i)) = ∏ᶠ v, Eu.acoef R i t μ 𝓕 v (F.1 v) := by
  obtain ⟨k, hk, e⟩ := out_famCls R i F
  rw [e, Model.coef_mul_lev R i t hLF μ 𝓕 _ k hk, coef_famProd R i t hM hLF hVN hμ F.1 F.2]

theorem trPair_out (R : RealDat D A Ks) (i : Fin D.R.m) (hT : TransLaws R i)
    (F : {F : ∀ v, Eu.LX R i v // {w | F w ≠ Eu.lx0 R i w}.Finite}) (x y) :
    trPair R i ((famCls R i F).out : GfC (Wc D i)) x y = ⟪x, Eu.Bfam R i F.1 y⟫_ℂ := by
  obtain ⟨k, hk, e⟩ := out_famCls R i F
  have e2 := hT.2.2.2.1 _ (famProd_mem R i F.1) 1 (one_mem _) k hk x y
  rw [one_mul] at e2
  rw [e, e2, trPair_eq_bop hT (famProd_mem R i F.1)]
  unfold Eu.Bfam
  rfl

theorem hasSum_reindex {X Y : Type} (e : X → Y) (he : Function.Bijective e) (a s : ℂ) (c p : Y → ℂ) (c' p' : X → ℂ)
    (hc : ∀ F, c (e F) = c' F) (hp : ∀ F, p (e F) = p' F) (H : HasSum (fun q => a * (c q * p q)) s) :
    HasSum (fun F => a * (c' F * p' F)) s := by
  have H1 := (Equiv.ofBijective _ he).hasSum_iff.2 H
  refine (congrArg (fun f => HasSum f s) (funext fun F => ?_)).mp H1
  rw [← hc, ← hp]
  rfl

set_option maxHeartbeats 1000000 in

theorem hasSum_families : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ i t, LevProd R i → TransLaws R i → FinMult R i t → LevFix R i t → VecNe R i t → FinSum R i t → ∀ th, IsRaw R i t th → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∃ a : ℝ, 0 < a ∧ ∀ x y, HasSum (fun F : {F : ∀ v, Eu.LX R i v // {w | F w ≠ Eu.lx0 R i w}.Finite} => (a : ℂ) * ((∏ᶠ v, Eu.acoef R i t μ 𝓕 v (F.1 v)) * ⟪x, Eu.Bfam R i F.1 y⟫_ℂ)) ⟪LinearMap.adjoint th x, LinearMap.adjoint th y⟫_ℂ := by
  intro D G _ _ Pl0 T A Ks _ _ _ R i t hP hT hM hLF hVN hS th hth μ 𝓕 hμ
  refine (hS th hth μ 𝓕 hμ).imp fun a H => ⟨H.1, fun x y => ?_⟩
  exact hasSum_reindex (famCls R i) (famCls_bijective R i hP) _ _ _ _ _ _ (coef_out R i t hM hLF hVN hμ)
    (fun F => trPair_out R i hT F x y) (H.2 x y)

end GlobalTheory.RawLift.FamSum

end
