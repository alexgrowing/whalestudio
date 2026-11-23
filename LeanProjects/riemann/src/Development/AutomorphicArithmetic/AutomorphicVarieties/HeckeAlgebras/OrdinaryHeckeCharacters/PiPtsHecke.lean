import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CsdSsOfFull
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CoefficientRepTrivialOnUnramified
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.SpecIntIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PartAct0
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CoreEig
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.HiComm
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.HiAlgUnit
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PiBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.BnRepLin
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.MemIsotypicOfInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecOfRecLiteralStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

attribute [local instance 2000] UpperTheory.V.W.coefLocal

private theorem piPts_hecke {A M ι : Type} [CommRing A] [AddCommGroup M] [Module A M] (Y : Submodule A M)
    (op : ι → Module.End A M) (φ : Module.End A M) (h : ∀ i, Commute φ (op i)) (t : heckeAlg Y op) :
    ∀ y y' : Y, (y' : M) = φ y → ((t : Module.End A Y) y' : M) = φ ((t : Module.End A Y) y) := by
  obtain ⟨t, ht⟩ := t
  change ∀ y y' : Y, (y' : M) = φ y → (t y' : M) = φ (t y)
  induction ht using Algebra.adjoin_induction with
  | mem t ht =>
    obtain ⟨i, hi⟩ := ht
    intro y y' e
    rw [hi, hi, e]
    exact (LinearMap.congr_fun (h i).eq y).symm
  | algebraMap a =>
    intro y y' e
    simp [Module.algebraMap_end_apply, e]
  | add s t _ _ hs ht =>
    intro y y' e
    simp only [LinearMap.add_apply, Submodule.coe_add, map_add, hs y y' e, ht y y' e]
  | mul s t _ _ hs ht => exact fun y y' e => hs _ _ (ht y y' e)

private theorem piPts_chi {n : ℕ} {A G : Type} [CommRing A] [Group G] (ρ : G →* Matrix (Fin n) (Fin n) A) (g : G) :
    (W.GDet.ofRep ρ).chi (MonoidAlgebra.single g 1) = (ρ g).charpoly := by
  change (W.GDet.repAlg ρ (Polynomial A) _).det = _
  rw [map_sub, MonoidAlgebra.mapRingHom_single, Matrix.charpoly]
  congr 1
  ext i j : 2
  by_cases h : i = j <;> simp [W.GDet.repAlg, Matrix.charmatrix, h, Matrix.one_apply, Matrix.diagonal_apply]

private theorem piPts_coord {A N V κ : Type} [CommRing A] [AddCommGroup N] [Module A N] [AddCommGroup V] [Module ℂ V]
    (b : Module.Basis κ A N) (φ : A →+* ℂ) (s : N → V) (ha : ∀ x y, s (x + y) = s x + s y)
    (hs : ∀ a x, s (a • x) = φ a • s x) (hi : LinearIndependent ℂ fun i => s (b i)) (z : N) (hz : s z = 0) (i : κ) :
    φ (b.repr z i) = 0 := by
  let S : N →+ V := AddMonoidHom.mk' s ha
  by_cases h : i ∈ (b.repr z).support
  · refine linearIndependent_iff'.1 hi (b.repr z).support (fun i => φ (b.repr z i)) ?_ i h
    have : S z = S (Finsupp.linearCombination A b (b.repr z)) := by rw [b.linearCombination_repr]
    rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum] at this
    rw [← hz]
    exact (Finset.sum_congr rfl fun i _ => (hs _ _).symm).trans this.symm
  · rw [Finsupp.notMem_support_iff.1 h, map_zero]

private theorem piPts_rp {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) {A : Type} [CommRing A] {m : ℕ}
    (τ : X.Ub →* GL (Fin m) A) (u : X.Ub) (b : Gp) : Commute (X.ra τ u) (X.rp A m b) := by
  refine LinearMap.ext fun f => funext fun x => ?_
  change X.ra τ u (X.rp A m b f) x = X.ra τ u f (x * (1, b))
  rw [Frame.ra_apply, Frame.ra_apply]
  change Matrix.mulVec _ (f _) = _
  simp [mul_assoc]

private theorem piPts_mm {n : ℕ} {A B C G : Type} [CommRing A] [CommRing B] [CommRing C] [Group G] (D : W.GDet n A G)
    (f : A →+* B) (f' : B →+* C) : (D.map f).map f' = D.map (f'.comp f) :=
  W.GDet.ext fun _ _ _ _ => rfl

section

variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {c : Coef l} (H : HSet L Ω l n c)

private theorem piPts_comm (hH : H.Ax) (A : Type) [CommRing A] [Algebra c.O A] (q : H.Q) (g : GLw n (H.wq q)) (i : H.Op) :
    Commute (H.X.ra (H.τA A) (H.sec (H.wq q) g)) (H.op A i) := by
  rcases i with ⟨w, j⟩ | ⟨v, j⟩
  · refine finsum_induction (fun t => Commute (H.X.ra (H.τA A) (H.sec (H.wq q) g)) t) (Commute.zero_right _)
      (fun _ _ => Commute.add_right) fun i => ?_
    exact (hH.sectionsCommuteAtSplit q w.1 w.2 g _).map (H.X.ra (H.τA A))
  · refine finsum_induction (fun t => Commute (H.X.ra (H.τA A) (H.sec (H.wq q) g)) t) (Commute.zero_right _)
      (fun _ _ => Commute.add_right) fun i => ?_
    exact piPts_rp H.X (H.τA A) _ _

private theorem piPts_iso (Lit : GlobalTheory.Mem.LiteralAutomorphy.LitN) (hH : H.Ax) (ι : Qbar l ≃+* ℂ) (lam : Wt L l n) {d : ℕ}
    (ξ : GV n H.Sl →* GL (Fin d) ℂ) (Y Y' : H.Part ι lam ξ)
    (h : W.GDet.ofRep (W.mat Y.r) = W.GDet.ofRep (W.mat Y'.r)) (q : H.Q) :
    Nonempty ((Y.σq q).ρ.Equiv (Y'.σq q).ρ) := by
  obtain ⟨P, hP⟩ := AlgebraTools.Det.bnRep (W.mat Y.r) (W.mat Y'.r) Y.ss Y'.ss fun g => by
    rw [← piPts_chi, ← piPts_chi, h]
  obtain ⟨B, hB⟩ : ∃ B : ValuationSubring Ω, IsPlaceOver B (H.wq q) := exists_isPlaceOver Ω _
  have Lo := Lit.loc
  obtain ⟨rc, hrc0⟩ := Lo.llc L Ω B _ hB
  have hrc : IsRec hB rc := GlobalTheory.T.rec_of_rec_literal Lo.dzc Lo.dzi Lo.exh Lo.multi Lo.cos Lo.zel Lo.geo Lo.bz L Ω B _ hB rc hrc0
  have h1 := (Y'.atQ q B hB rc hrc).of_conj (hH.Q_away q) (r' := Y.r.comp H.prj) P fun g => Units.ext (hP _)
  have h2 := (Y.atQ q B hB rc hrc).unique (hH.Q_away q) h1
  obtain ⟨a, ha, ε, -, hL⟩ := hrc
  have h3 := congrArg (fun x => x.nu (-(((1 - (n : ℝ)) / 2 : ℝ) : ℂ))) (hL.bij.1 h2)
  simp only [algNorm, IrrGL.nu_nu, add_neg_cancel, IrrGL.nu_zero] at h3
  exact IrrGL.of_eq_of.1 h3

private theorem piPts_dir (hH : H.Ax) (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ)
    (hθ : H.IsWt θ) (a : H.Op → c.O) (s : Finset (⨆ K, H.MK θ a K : Submodule A (H.X.Fn A H.m))) :
    ∃ K, ∀ f ∈ s, (f : H.X.Fn A H.m) ∈ H.MK θ a K := by
  classical
  obtain ⟨ρ, -, h1, h2, -⟩ := piBasic L Ω l n c H hH A θ hθ a
  have mono : ∀ K K' : H.Lev, (∀ q, K'.1 q ≤ K.1 q) → H.MK θ a K ≤ H.MK θ a K' := fun K K' h => by
    rw [← h1, ← h1]
    exact Submodule.map_mono fun v hv u hu => hv u fun q hq => h q (hu q hq)
  induction s using Finset.induction with
  | empty => exact ⟨(h2 0).choose, by simp⟩
  | insert f s _ ih =>
    obtain ⟨K, hK⟩ := ih
    obtain ⟨K', hK'⟩ := h2 f
    let K'' : H.Lev := ⟨fun q => K.1 q ⊓ K'.1 q, fun q => ⟨(K.2 q).1.inter (K'.2 q).1,
      (K.2 q).2.inter_right ((K'.1 q).isClosed_of_isOpen (K'.2 q).1)⟩⟩
    refine ⟨K'', fun x hx => ?_⟩
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact mono K' K'' (fun q => inf_le_right) hK'
    · exact mono K K'' (fun q => inf_le_left) (hK x hx)

end

private theorem piPts_abs {M V R G Lev X : Type} {I : Type 1} [AddCommGroup V] [Module ℂ V]
    (s : M → V) (z : M) (hz : s z ≠ 0) (α : R → M → M) (ρ : G → M → M) (π : G → V →ₗ[ℂ] V) (mem : Lev → M → Prop)
    (dir : ∀ u : Finset M, ∃ K, ∀ f ∈ u, mem K f) (EK : Lev → Submodule ℂ V) (hEK : ∀ K f, mem K f → s f ∈ EK K)
    (hEK' : ∀ K, EK K ≤ Submodule.span ℂ (s '' {f | mem K f})) (Yp : I → Submodule ℂ V) (χ : X → R → ℂ) (rel : I → X → Prop)
    (h1 : ∀ g f, s (ρ g f) = π g (s f)) (h2 : ∀ g t f, α t (ρ g f) = ρ g (α t f))
    (lev : ∀ K, mem K z → ∃ act : R → Module.End ℂ (EK K), (∀ t f hf, (act t ⟨s f, hEK K f hf⟩ : V) = s (α t f)) ∧
      (EK K ≤ ⨆ i, Yp i ⊓ EK K) ∧
      ∀ i, Yp i ⊓ EK K ≠ ⊥ → ∃ x, rel i x ∧ ∀ t (F : EK K), (F : V) ∈ Yp i → act t F = χ x t • F) :
    ∃ (i0 : I) (x0 : X) (Y : Submodule ℂ V) (p : V →ₗ[ℂ] Y), rel i0 x0 ∧ (∀ g, ∀ F ∈ Y, π g F ∈ Y) ∧ p (s z) ≠ 0 ∧
      (∀ t f, p (s (α t f)) = χ x0 t • p (s f)) ∧ (∀ g f, (p (s (ρ g f)) : V) = π g (p (s f))) ∧
      ∀ Z : Submodule ℂ V, (∀ i x, rel i x → χ x = χ x0 → Yp i ≤ Z) → Y ≤ Z := by
  classical
  have hT : ∀ t, ∃ T : V →ₗ[ℂ] V, ∀ f, T (s f) = s (α t f) := fun t => by
    refine PiLin.exists_desc _ _ fun u hu => ?_
    obtain ⟨K, hK⟩ := dir (insert z u.support)
    obtain ⟨act, a1, -⟩ := lev K (hK z (Finset.mem_insert_self _ _))
    have hm : ∀ f : u.support, mem K f := fun f => hK _ (Finset.mem_insert_of_mem f.2)
    rw [Finsupp.linearCombination_apply, Finsupp.sum, ← Finset.sum_coe_sort] at hu ⊢
    have h0 : ∑ f : u.support, u f • (⟨s f, hEK K f (hm f)⟩ : EK K) = 0 := Subtype.ext (by
      rw [Submodule.coe_sum]; exact hu)
    have h3 := congrArg (fun F => (act t F : V)) h0
    simp only [map_sum, map_smul, map_zero, Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_zero] at h3
    rw [← h3]
    exact Finset.sum_congr rfl fun f _ => by rw [a1 t f (hm f)]
  choose T hT using hT
  let E := Submodule.span ℂ (Set.range s)
  have hE : ∀ f, s f ∈ E := fun f => Submodule.subset_span ⟨f, rfl⟩
  let J := {j : I × X × Submodule ℂ V // j.2.2 ≤ Yp j.1 ⊓ E ∧ rel j.1 j.2.1 ∧ ∀ t, ∀ F ∈ j.2.2, T t F = χ j.2.1 t • F}
  have hsup : E = ⨆ j : J, j.1.2.2 := by
    refine le_antisymm (Submodule.span_le.2 ?_) (iSup_le fun j => j.2.1.trans inf_le_right)
    rintro _ ⟨f, rfl⟩
    obtain ⟨K, hK⟩ := dir {z, f}
    obtain ⟨act, a1, a3, a4⟩ := lev K (hK z (by simp))
    have hle : EK K ≤ E := (hEK' K).trans (Submodule.span_mono (Set.image_subset_range _ _))
    have hsp : Submodule.span ℂ (s '' {f | mem K f}) ≤ EK K := Submodule.span_le.2 (by
      rintro _ ⟨y, hy, rfl⟩
      exact hEK K y hy)
    have hact : ∀ t F (hF : F ∈ Submodule.span ℂ (s '' {f | mem K f})), T t F = act t ⟨F, hsp hF⟩ := fun t F hF => by
      induction hF using Submodule.span_induction with
      | mem F hF =>
        obtain ⟨y, hy, rfl⟩ := hF
        exact (hT t y).trans (a1 t y hy).symm
      | zero => exact (map_zero _).trans (congrArg Subtype.val (map_zero (act t))).symm
      | add F F' hF hF' h h' =>
        rw [map_add, h, h']
        exact (congrArg Subtype.val (map_add (act t) ⟨F, hsp hF⟩ ⟨F', hsp hF'⟩)).symm
      | smul u F hF h =>
        rw [map_smul, h]
        exact (congrArg Subtype.val (map_smul (act t) u ⟨F, hsp hF⟩)).symm
    refine (show EK K ≤ ⨆ j : J, j.1.2.2 from ?_) (hEK K f (hK f (by simp)))
    refine a3.trans (iSup_le fun i => ?_)
    by_cases hY : Yp i ⊓ EK K = ⊥
    · rw [hY]; exact bot_le
    · obtain ⟨x, b1, b2⟩ := a4 i hY
      exact le_iSup (fun j : J => j.1.2.2) ⟨(i, x, Yp i ⊓ EK K), inf_le_inf_left _ hle, b1, fun t F hF => by
        rw [hact t F (hEK' K hF.2), b2 t ⟨F, hF.2⟩ hF.1]; rfl⟩
  obtain ⟨j0, Y, p, -, y1, y2, y3, y4, y5⟩ := PiLin.exists_proj (J := J) T π E
    (fun g => show E ≤ E.comap (π g) from Submodule.span_le.2 (by
      rintro _ ⟨f, rfl⟩
      change π g (s f) ∈ E
      rw [← h1]
      exact hE _))
    (fun t g F hF => LinearMap.eqOn_span' (f := T t ∘ₗ π g) (g := π g ∘ₗ T t) (by
      rintro _ ⟨f, rfl⟩
      simp only [LinearMap.comp_apply]
      rw [← h1, hT, hT, h2, h1]) hF)
    (fun j => j.1.2.2) (fun j => χ j.1.2.1) (fun j => j.2.2.2) hsup (s z) (hE z) hz
  refine ⟨j0.1.1, j0.1.2.1, Y, p, j0.2.2.1, y1, y2, fun t f => ?_, fun g f => ?_, fun Z hZ => y5.trans (iSup_le fun j => ?_)⟩
  · rw [← hT, y3 t _ (hE f)]
  · rw [h1, y4 g _ (hE f)]
  · exact (j.1.2.1.trans inf_le_left).trans (hZ _ _ j.1.2.2.1 j.2)

private theorem piPts_sum {H Y V : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [AddCommGroup Y] [Module ℂ Y]
    [AddCommGroup V] [Module ℂ V] (σ : SmIrr H) (π : Representation ℂ H Y) (ρ : Representation ℂ H V)
    (j : Y →ₗ[ℂ] V) (hj : Function.Injective j) (he : ∀ g y, j (π g y) = ρ g (j y))
    (h : ∀ Z : Submodule ℂ V, (∀ (W : Submodule ℂ V) (σ' : SmIrr H), IsoSum ρ W σ' → Nonempty (σ.ρ.Equiv σ'.ρ) → W ≤ Z) →
      ∀ y, j y ∈ Z) : IsoSum π ⊤ σ := by
  intro F _
  have := PiLin.iso_sub σ.ρ π ρ σ.irred j hj he (h _ ?_) F
  · refine SetLike.le_def.1 (iSup_le fun f => ?_) this
    exact le_iSup_of_le ⟨f.1, f.2, le_top⟩ le_rfl
  · rintro W σ' hW ⟨e⟩
    refine le_trans hW (iSup_le fun f => ?_)
    refine le_iSup_of_le ⟨f.1 ∘ₗ e.toLinearEquiv.toLinearMap, fun g v => ?_⟩ ?_
    · exact (congrArg f.1 (e.toIntertwiningMap.isIntertwining _ _ g v)).trans (f.2.1 g _)
    · exact (LinearMap.range_comp_of_range_eq_top _ e.toLinearEquiv.range).ge

set_option maxHeartbeats 800000 in
theorem UpperTheory.V.Hi.piPts :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ) (P : Wt L l n → (H.Gq →* GL (Fin n) (Qbar l)) → Prop), H.Aut ι P →
    ∀ lam0 ∈ H.admitted, H.DenseWt θ lam0 → ∀ (a : H.Op → c.O) [DecidableEq H.Q] (ρ : Representation A (GV n H.wq) (⨆ K, H.MK θ a K : Submodule A (H.X.Fn A H.m))), (∀ q g f, (ρ (Pi.mulSingle q g) f : H.X.Fn A H.m) = H.X.ra (H.τA A) (H.sec (H.wq q) g) f) → ∀ (R : Type) [CommRing R] (D : W.GDet n R H.Gq) (α : R →+* Module.End A (⨆ K, H.MK θ a K : Submodule A (H.X.Fn A H.m))), (∀ (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))] [Alg.IsCO c.O (H.TK θ a K)], ∃ (f : R →+* H.TK θ a K) (ψ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* (H.TK θ a K)ˣ), H.IsUniv θ a K (maximalIdeal _) (D.map f) ψ ∧ ∀ t (y : H.MK θ a K) (z : (⨆ K, H.MK θ a K : Submodule A (H.X.Fn A H.m))), (z : H.X.Fn A H.m) = y → (α t z : H.X.Fn A H.m) = ((f t : Module.End A (H.MK θ a K)) y : H.MK θ a K)) → ∀ z : (⨆ K, H.MK θ a K : Submodule A (H.X.Fn A H.m)), z ≠ 0 → ∃ (x : R →+* Qbar l) (r : H.Gq →* GL (Fin n) (Qbar l)) (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (π : Representation ℂ (GV n H.wq) Y) (sp : (⨆ K, H.MK θ a K : Submodule A (H.X.Fn A H.m)) →+ Y) (σ : ∀ q, SmIrr (GLw n (H.wq q))), sp z ≠ 0 ∧ Continuous r ∧ D.map x = W.GDet.ofRep (W.mat r) ∧ (∀ t y, sp (α t y) = ι (x t) • sp y) ∧ (∀ g y, sp (ρ g y) = π g (sp y)) ∧ (∀ q, IsoSum (π.comp (MonoidHom.mulSingle (fun q => GLw n (H.wq q)) q)) ⊤ (σ q)) ∧ ∀ q (B : ValuationSubring Ω) (h : IsPlaceOver B (H.wq q)) (rc : IrrGL ((H.wq q).adicCompletion L) → WD h), IsRec h rc → UpperTheory.V.Lev.WO ι (r.comp H.prj) (rc (algNorm (σ q))) := by
  intro Lit L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ hθ ι P hP lam hlam hden a _ ρ hρ R _ D α hα z hz
  have dir := piPts_dir H hH A θ hθ a
  have hcomm := hiComm L Ω l n c H hH A θ hθ
  have hord : ∀ K, H.MK θ a K ≤ H.X.Ord (H.τA A) θ (H.lev K) := fun K => inf_le_left
  obtain ⟨K0, hK0⟩ := dir {z}
  replace hK0 := hord K0 (hK0 z (Finset.mem_singleton_self z))
  haveI := (hcomm K0).2.2.1
  let b := Module.Free.chooseBasis A (H.X.Ord (H.τA A) θ (H.lev K0))
  obtain ⟨i0, hi0⟩ : ∃ i, b.repr ⟨z, hK0⟩ i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have : (⟨z, hK0⟩ : H.X.Ord (H.τA A) θ (H.lev K0)) = 0 := b.repr.injective (by rw [map_zero]; exact Finsupp.ext hcon)
    exact hz (Subtype.ext (congrArg Subtype.val this :))
  obtain ⟨x0, hgood, hx0⟩ : ∃ x0 : A →ₐ[c.O] Qbar l, H.Good θ x0 lam ∧ x0 (b.repr ⟨z, hK0⟩ i0) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hi0 (hden _ hcon)
  obtain ⟨d, ξ, c0, sp, hsp⟩ := spec L Ω l n c H hH A θ hθ ι x0 lam hgood.2.1
  have hspz : sp z ≠ 0 := fun h => hx0 <| ι.injective <| by
    rw [map_zero]
    exact piPts_coord b (ι.toRingHom.comp x0.toRingHom) (fun f => sp f) (fun f f' => hsp.add K0 f f.2 f' f'.2)
      (fun u f => hsp.smul K0 f f.2 u) (hsp.indep K0 _ b) ⟨z, hK0⟩ h i0
  classical
  let s : (⨆ K, H.MK θ a K : Submodule A (H.X.Fn A H.m)) →+ (Fin H.m → H.X.Fn ℂ d) := AddMonoidHom.mk' (fun f => sp f) fun f f' => by
    obtain ⟨K, hK⟩ := dir {f, f'}
    exact hsp.add K f (hord K (hK f (by simp))) f' (hord K (hK f' (by simp)))
  have hs : ∀ f, s f = sp f := fun _ => rfl
  let EK : H.Lev → Submodule ℂ (Fin H.m → H.X.Fn ℂ d) := fun K => Submodule.span ℂ (sp '' H.MK θ a K)
  have hEK : ∀ K (f : (⨆ K, H.MK θ a K : Submodule A (H.X.Fn A H.m))), (f : H.X.Fn A H.m) ∈ H.MK θ a K → s f ∈ EK K :=
    fun K f hf => Submodule.subset_span ⟨f, hf, rfl⟩
  have lev : ∀ K, (z : H.X.Fn A H.m) ∈ H.MK θ a K → ∃ act : R → Module.End ℂ (EK K),
      (∀ t (f : (⨆ K, H.MK θ a K : Submodule A (H.X.Fn A H.m))) (hf : (f : H.X.Fn A H.m) ∈ H.MK θ a K),
        (act t ⟨s f, hEK K f hf⟩ : Fin H.m → H.X.Fn ℂ d) = s (α t f)) ∧
      (∀ t q g (f : (⨆ K, H.MK θ a K : Submodule A (H.X.Fn A H.m))), (f : H.X.Fn A H.m) ∈ H.MK θ a K →
        (ρ (Pi.mulSingle q g) f : H.X.Fn A H.m) ∈ H.MK θ a K → α t (ρ (Pi.mulSingle q g) f) = ρ (Pi.mulSingle q g) (α t f)) ∧
      (EK K = ⨆ Y : {Y : H.Part ι lam ξ // P lam Y.r}, Y.1.Y ⊓ EK K) ∧
      ∀ Y : H.Part ι lam ξ, Y.Y ⊓ EK K ≠ ⊥ → ∃ x : R →+* Qbar l, D.map x = W.GDet.ofRep (W.mat Y.r) ∧
        ∀ t (F : EK K), (F : Fin H.m → H.X.Fn ℂ d) ∈ Y.Y → act t F = ι (x t) • F := by
    intro K hzK
    haveI : Fact (CommOn (H.MK θ a K) (H.op A)) := ⟨((hcomm K).2.2.2 a).1⟩
    obtain ⟨_, -⟩ := hiAlg L Ω l n c H hH A θ hθ a K fun h => hz (Subtype.ext (by rwa [h] at hzK))
    obtain ⟨f, ψ, huniv, hf⟩ := hα K
    obtain ⟨hE, act, a1, a2, -, -, a5⟩ := partAct0 Lit L Ω l n c H hH A θ hθ ι P hP x0 lam d ξ c0 sp hsp hlam a K (EK K) rfl
    refine ⟨fun t => act (f t), fun t y hy => ?_, fun t q g y hy hy' => Subtype.ext ?_, hE.resolve_right (not_not.2 hgood),
      fun Y hY => ?_⟩
    · exact (a1 _ ⟨y, hy⟩ _ rfl).trans (congrArg sp (hf t ⟨y, hy⟩ y rfl).symm)
    · rw [hρ, hf t ⟨y, hy⟩ y rfl, hf t ⟨_, hy'⟩ _ rfl]
      exact piPts_hecke _ _ _ (piPts_comm H hH A q g) (f t) _ _ (hρ q g y)
    · obtain ⟨y, -, hy⟩ := a5 hgood Y hY
      obtain ⟨F, hF, hF0⟩ := (Submodule.ne_bot_iff _).1 hY
      refine ⟨y.toRingHom.comp f, ?_, fun t F hF => hy _ F hF⟩
      refine Eq.trans (piPts_mm D f _).symm
        (coreEig Lit L Ω l n c H hH A θ hθ ι a K _ ψ huniv y lam d ξ Y F hF.1 hF0 fun w j => ?_).1
      rw [← a2 _ ⟨F, hF.2⟩, hy _ ⟨F, hF.2⟩ hF.1]
      rfl
  let π0 : Representation ℂ (GV n H.wq) (Fin H.m → H.X.Fn ℂ d) := (H.X.raF d (H.τC ι)).comp
    (MonoidHom.noncommPiCoprod (fun q => H.sec (H.wq q)) fun q q' h => hH.Q_Q q q' h)
  have hπ0 : ∀ q g, π0 (Pi.mulSingle q g) = H.atW ι d (H.wq q) g := fun q g =>
    congrArg (H.X.raF d (H.τC ι)) (MonoidHom.noncommPiCoprod_mulSingle (fun q => H.sec (H.wq q)) q g)
  have hsρ : ∀ g, (∀ f, s (ρ g f) = π0 g (s f)) ∧ ∀ t f, α t (ρ g f) = ρ g (α t f) := fun g => by
    let S : Submonoid (GV n H.wq) :=
      { carrier := {g | (∀ f, s (ρ g f) = π0 g (s f)) ∧ ∀ t f, α t (ρ g f) = ρ g (α t f)}
        one_mem' := by simp
        mul_mem' := fun {g g'} h h' => ⟨fun f => by simp only [map_mul, Module.End.mul_apply, h.1, h'.1],
          fun t f => by simp only [map_mul, Module.End.mul_apply, h.2, h'.2]⟩ }
    refine Submonoid.pi_mem_of_mulSingle_mem (H := S) g fun q => ⟨fun f => ?_, fun t f => ?_⟩
    · obtain ⟨K, hK⟩ := dir {f, ρ (Pi.mulSingle q (g q)) f}
      rw [hs, hs, hπ0, hρ]
      exact hsp.act K K q _ f (hord K (hK f (by simp))) (by rw [← hρ]; exact hord K (hK _ (by simp)))
    · obtain ⟨K, hK⟩ := dir {z, f, ρ (Pi.mulSingle q (g q)) f}
      obtain ⟨-, -, a2, -⟩ := lev K (hK z (by simp))
      exact a2 t q _ f (hK _ (by simp)) (hK _ (by simp))
  obtain ⟨Y0, x, Y, p, y0, y1, y2, y3, y4, y5⟩ := piPts_abs (I := H.Part ι lam ξ) (X := R →+* Qbar l) s z hspz
    (fun t f => α t f) (fun g f => ρ g f) (fun g => π0 g) (fun K f => (f : H.X.Fn A H.m) ∈ H.MK θ a K) dir EK hEK
    (fun K => Submodule.span_mono fun _ ⟨y, hy, e⟩ => ⟨⟨y, Submodule.mem_iSup_of_mem K hy⟩, hy, e⟩)
    (fun Y => Y.Y) (fun x t => ι (x t)) (fun Y x => D.map x = W.GDet.ofRep (W.mat Y.r))
    (fun g => (hsρ g).1) (fun g => (hsρ g).2) fun K hK => by
      obtain ⟨act, a1, -, a3, a4⟩ := lev K hK
      refine ⟨act, a1, a3.le.trans (iSup_le fun Y => le_iSup (fun Y : H.Part ι lam ξ => Y.Y ⊓ EK K) Y.1), fun Y hY => ?_⟩
      obtain ⟨x, b1, b2⟩ := a4 Y hY
      exact ⟨x, b1, b2⟩
  refine ⟨x, Y0.r, Y, inferInstance, inferInstance, π0.subrepresentation Y y1, p.toAddMonoidHom.comp s,
    Y0.σq, y2, Y0.cont, y0, y3, fun g y => Subtype.ext (y4 g y), fun q => ?_, Y0.atQ⟩
  refine piPts_sum _ _ (H.atW ι d (H.wq q)) Y.subtype Y.subtype_injective
    (fun g y => LinearMap.congr_fun (hπ0 q g) y) fun Z hZ y => y5 Z (fun Y1 x1 b1 b2 => ?_) y.2
  have hx : x1 = x := RingHom.ext fun t => ι.injective (congrFun b2 t)
  exact hZ _ _ (Y1.isoQ q) (piPts_iso H Lit hH ι lam ξ Y0 Y1 (by rw [← y0, ← b1, hx]) q)
