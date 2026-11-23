import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.TwistRatios.IneInf
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.EqOfTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FlagWD
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.OrdCharIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.EpsArt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.WeilGroupDenseInGaloisGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGenericOfIsLocComp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamAndJumpsRankOneLAdicCharacter
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdeleEmbeddingExtension
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDEqSumOfAgree

import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.WeightKernels.GoodSet

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.W (Plc Lp)
open scoped Polynomial
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.V.Z.Sym.AboveWeight

section

theorem norm_one {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] [NormedField K]
    (ψ : Γ →* Kˣ) (hψ : Continuous fun s => (ψ s : K)) (s : Γ) : ‖(ψ s : K)‖ = 1 := by
  have key : ∀ t, ‖(ψ t : K)‖ ≤ 1 := fun t => by
    obtain ⟨C, hC⟩ := (isCompact_range hψ.norm).bddAbove
    refine not_lt.1 fun hlt => ?_
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt C hlt
    have h1 := hC ⟨t ^ m, rfl⟩
    simp only [map_pow, Units.val_pow_eq_pow_val, norm_pow] at h1
    exact absurd hm (not_lt.2 h1)
  refine le_antisymm (key s) ?_
  have h2 := key s⁻¹
  rw [map_inv, Units.val_inv_eq_inv_val, norm_inv] at h2
  exact (inv_le_one₀ (norm_pos_iff.2 (ψ s).ne_zero)).1 h2

theorem open_ker_of_pow {Γ K : Type} [Group Γ] [TopologicalSpace Γ] [Field K] [TopologicalSpace K] [T1Space K]
    (ph : Γ →* Kˣ) (hc : Continuous fun s => (ph s : K)) {k : ℕ} (hk : 0 < k) (hp : ∀ s, ph s ^ k = 1) :
    IsOpen (ph.ker : Set Γ) := by
  classical
  let S : Set K := ((Polynomial.nthRootsFinset k (1 : K) : Finset K) : Set K) \ {1}
  have hS : IsClosed S := (Finset.finite_toSet _).subset Set.diff_subset |>.isClosed
  have e : (ph.ker : Set Γ) = (fun s => (ph s : K)) ⁻¹' Sᶜ := by
    ext s
    have h1 : (ph s : K) ^ k = 1 := by rw [← Units.val_pow_eq_pow_val, hp, Units.val_one]
    have h2 : (ph s : K) ∈ ((Polynomial.nthRootsFinset k (1 : K) : Finset K) : Set K) :=
      Finset.mem_coe.2 ((Polynomial.mem_nthRootsFinset hk 1).2 h1)
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_compl_iff, S, Set.mem_diff, Set.mem_singleton_iff, not_and, not_not]
    exact ⟨fun h _ => by rw [h, Units.val_one], fun h => Units.ext (h h2)⟩
  rw [e]
  exact hS.isOpen_compl.preimage hc

section

variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
  {w : Plc L} {A : ValuationSubring Ω} {h : IsPlaceOver A w} {a : Weil h →* (w.adicCompletion L)ˣ}

theorem algPow_add (d e : (L →+* Qbar l) → ℤ) (x : (w.adicCompletion L)ˣ) :
    algPow w (d + e) (x : w.adicCompletion L) = algPow w d (x : w.adicCompletion L) * algPow w e (x : w.adicCompletion L) := by
  haveI := GlobalTheory.HeckeGal.finite_contEmb (l := l) w
  unfold algPow
  rw [← finprod_mul_distrib (Set.toFinite _) (Set.toFinite _)]
  exact finprod_congr fun j => by rw [Pi.add_apply, zpow_add₀ ((_root_.map_ne_zero j.1).2 x.ne_zero)]

theorem algPow_const (c : ℤ) (x : (w.adicCompletion L)ˣ) :
    algPow w (fun _ : L →+* Qbar l => c) (x : w.adicCompletion L) =
      algPow w (fun _ : L →+* Qbar l => 1) (x : w.adicCompletion L) ^ c := by
  haveI := GlobalTheory.HeckeGal.finite_contEmb (l := l) w
  haveI := Fintype.ofFinite {j : w.adicCompletion L →+* Qbar l // Continuous j}
  unfold algPow
  rw [finprod_eq_prod_of_fintype, finprod_eq_prod_of_fintype, ← Finset.prod_zpow]
  exact Finset.prod_congr rfl fun j _ => by rw [zpow_one]

theorem eps_cont (A : ValuationSubring Ω) : Continuous ((cycBar L Ω l).comp (Dec (F := L) A).subtype) :=
  ((Continuous.units_map ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom
    ((continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val)).comp (continuous_cycZ L Ω l)).comp continuous_subtype_val

theorem flag_cont' {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] {n : ℕ} {r : Γ →* GL (Fin n) (Qbar l)}
    (hr : Continuous r) {ψ : Fin n → Γ →* (Qbar l)ˣ} (hf : W.HasFlag r ψ) (i : Fin n) : Continuous (ψ i) := by
  obtain ⟨g, hg⟩ := hf
  have h1 : Continuous fun s => (ψ i s : Qbar l) :=
    ((Units.continuous_val.comp ((continuous_const.mul hr).mul continuous_const)).matrix_elem i i).congr fun s => (hg s).2 i
  exact Units.continuous_iff.2 ⟨h1, (h1.comp continuous_inv).congr fun s => by simp⟩

theorem locAlg (H : GlobalTheory.Published.GlobalArtinReciprocity) (h : IsPlaceOver A w) (hw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal)
    (κ : Dec (F := L) A →* (Qbar l)ˣ) (hκ : Continuous κ) {k : ℕ} (hk : 0 < k) (c : ℤ)
    (hp : ∀ s : ↥(Dec (F := L) A), (s : G L Ω) ∈ Ine (F := L) A → κ s ^ k = (cycBar L Ω l s ^ c) ^ k) :
    W.IsLocAlg h κ fun _ => -c := by
  let ε := (cycBar L Ω l).comp (Dec (F := L) A).subtype
  let d : Ine (F := L) A →* Dec (F := L) A := (Subgroup.inclusion (Weil_le_Dec h)).comp (ineIncl h)
  have hdv : ∀ σ : Ine (F := L) A, ((d σ : Dec (F := L) A) : G L Ω) = σ := fun _ => rfl
  have hd : Continuous d := Topology.IsEmbedding.subtypeVal.continuous_iff.2 continuous_subtype_val
  refine ⟨((ε ^ c) * κ⁻¹).comp d, ?_, fun a ha σ => ?_⟩
  · refine open_ker_of_pow _ ?_ hk fun σ => ?_
    · have h1 : Continuous (fun s : Dec (F := L) A => ((ε ^ c * κ⁻¹) s)) :=
        ((eps_cont A).zpow c).mul hκ.inv
      exact Units.continuous_val.comp (h1.comp hd)
    · have h2 := hp (d σ) σ.2
      simp only [MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, mul_pow, inv_pow, h2]
      exact mul_inv_cancel _
  · have e1 : (cycBar L Ω l (ineIncl h σ : G L Ω) : Qbar l) = algPow w (fun _ => 1) (a (ineIncl h σ) : w.adicCompletion L) := by
      rw [UpperTheory.V.Loc.epsArt H h hw a ha, deg_ineIncl, zpow_zero, one_mul]
    have e2 : (∏ᶠ τ : W.Emb l w, τ.1 (a (ineIncl h σ) : w.adicCompletion L) ^ (- -c)) =
        algPow w (fun _ : L →+* Qbar l => c) (a (ineIncl h σ) : w.adicCompletion L) := by
      rw [neg_neg]; rfl
    rw [e2, algPow_const, ← e1]
    simp [ε, d]

theorem not_link (hv : A.valuation (l : Ω) < 1) {κ κ' : Dec (F := L) A →* (Qbar l)ˣ} {k : ℕ} (hk : 0 < k) {c c' : ℤ}
    (hp : ∀ s : ↥(Dec (F := L) A), (s : G L Ω) ∈ Ine (F := L) A → κ s ^ k = (cycBar L Ω l s ^ c) ^ k)
    (hp' : ∀ s : ↥(Dec (F := L) A), (s : G L Ω) ∈ Ine (F := L) A → κ' s ^ k = (cycBar L Ω l s ^ c') ^ k)
    (hc : c ≠ c' + 1) : κ ≠ κ' * (cycBar L Ω l).comp (Dec (F := L) A).subtype := by
  intro e
  obtain ⟨s, -, hs, hinf⟩ := UpperTheory.V.Z.Sym.Ga.ineInf L Ω l A hv ⊤ isOpen_univ
  refine hinf (isOfFinOrder_iff_zpow_eq_one.2 ⟨(c - c' - 1) * k, ?_, ?_⟩)
  · have : c - c' - 1 ≠ 0 := fun h0 => hc (by omega)
    exact mul_ne_zero this (by exact_mod_cast hk.ne')
  · have h1 := hp ⟨s, Ine_le_Dec A hs⟩ hs
    rw [e, MonoidHom.mul_apply, mul_pow, hp' ⟨s, Ine_le_Dec A hs⟩ hs] at h1
    simp only [MonoidHom.comp_apply, Subgroup.subtype_apply] at h1
    set x := cycBar L Ω l s
    have h2 : x ^ (c' * k + k : ℤ) = x ^ (c * k : ℤ) := by
      rw [zpow_add, zpow_mul, zpow_natCast, zpow_natCast, h1, zpow_mul, zpow_natCast]
    rw [sub_sub, sub_mul, zpow_sub, ← h2]
    simp [add_mul]
theorem sum_zero [Fintype (W.Emb l w)] (ha : IsLocalArtin h a) (d : (L →+* Qbar l) → ℤ)
    (χ : Dec (F := L) A →* (Qbar l)ˣ) (hχ : Continuous χ)
    (hv : ∀ s : Weil h, (χ (Subgroup.inclusion (Weil_le_Dec h) s) : Qbar l) = algPow w d (a s : w.adicCompletion L)) :
    ∑ j : W.Emb l w, d (j.1.comp (algebraMap L _)) = 0 := by
  haveI : CompactSpace (Dec (F := L) A) := isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact
  haveI : CharZero (w.adicCompletion L) := algebraRat.charZero _
  have hl : (l : Qbar l) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  obtain ⟨s, hs⟩ := ha.surj (Units.mk0 (l : w.adicCompletion L) (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero))
  have h1 := norm_one χ (Units.continuous_val.comp hχ) (Subgroup.inclusion (Weil_le_Dec h) s)
  rw [hv, hs, algPow, finprod_eq_prod_of_fintype] at h1
  simp only [Units.val_mk0, map_natCast] at h1
  have hp : ∀ (T : Finset (W.Emb l w)) (c : W.Emb l w → ℤ), ∏ j ∈ T, (l : Qbar l) ^ c j = (l : Qbar l) ^ ∑ j ∈ T, c j :=
    fun T c => T.cons_induction (by simp) fun j T hj ih => by rw [Finset.prod_cons, Finset.sum_cons, ih, zpow_add₀ hl]
  rw [hp, norm_zpow] at h1
  exact (zpow_eq_one_iff_right₀ (norm_nonneg _) (GlobalTheory.PlaceBridge.norm_l_lt_one (l := l)).ne).1 h1

theorem not_linked (H : GlobalTheory.Published.GlobalArtinReciprocity) (ι : Qbar l ≃+* ℂ) {n : ℕ} (hw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal)
    (ha : IsLocalArtin h a) {hh : Fin n → (L →+* Qbar l) → ℤ} (hm : ∀ τ, StrictMono fun j => hh j τ)
    {ω : Fin n → (w.adicCompletion L)ˣ →* ℂˣ} {ψ : Fin n → Dec (F := L) A →* (Qbar l)ˣ}
    (hO : ∀ j, OrdChar ι a (ω j) (hh j) (ψ j))
    (hne : ∀ i j, ψ i ≠ ψ j * (cycBar L Ω l).comp (Dec (F := L) A).subtype) (i j : Fin n) (hij : i ≠ j) :
    ω i ≠ ω j ∧ ω i ≠ ω j * absPow (w.adicCompletion L) 1 := by
  haveI := GlobalTheory.HeckeGal.finite_contEmb (l := l) w
  haveI := Fintype.ofFinite (W.Emb l w)
  let inc := Subgroup.inclusion (Weil_le_Dec h)
  let ε := (cycBar L Ω l).comp (Dec (F := L) A).subtype
  have hεc : Continuous ε := eps_cont A
  have hε : ∀ s : Weil h, (ε (inc s) : Qbar l) = ((normV w : ℕ) : Qbar l) ^ deg s * algPow w 1 (a s : w.adicCompletion L) :=
    UpperTheory.V.Loc.epsArt H h hw a ha
  have hv : ∀ k (s : Weil h), (ψ k (inc s) : Qbar l) = ι.symm (ω k (a s)) * algPow w (-hh k) (a s : w.adicCompletion L) :=
    fun k s => (hO k).val s _ rfl (Set.mem_univ _)
  have hN : Nonempty (W.Emb l w) := by
    by_contra hE
    haveI : IsEmpty (W.Emb l w) := not_nonempty_iff.1 hE
    haveI : CompactSpace (Dec (F := L) A) := isCompact_iff_compactSpace.1 (isClosed_Dec A).isCompact
    have h1 := norm_one ε (Units.continuous_val.comp hεc) (inc (frob h))
    rw [hε, deg_frob, zpow_one, algPow, finprod_of_isEmpty, mul_one, GlobalTheory.Pst.normV_eq_pow (l := l) hw, Nat.cast_pow, norm_pow] at h1
    have h2 := (pow_eq_one_iff_of_nonneg (norm_nonneg _) (fun h0 => by
      have := one_lt_normV w
      rw [GlobalTheory.Pst.normV_eq_pow (l := l) hw, h0] at this
      exact lt_irrefl _ this)).1 h1
    exact (GlobalTheory.PlaceBridge.norm_l_lt_one (l := l)).ne h2
  have hneg : ∀ d : W.Emb l w → ℤ, (∀ t, d t < 0) → ∑ t, d t ≠ 0 := fun d hd =>
    (Finset.sum_neg (fun t _ => hd t) Finset.univ_nonempty).ne
  constructor
  · intro e
    have h1 := sum_zero ha (hh j - hh i) (ψ i * (ψ j)⁻¹) ((hO i).cont.mul (hO j).cont.inv) fun s => by
      rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.mul_inv_eq_iff_eq_mul, hv, hv, e, mul_left_comm,
        ← algPow_add]
      congr 2
      abel
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · exact (Finset.sum_pos (fun t _ => sub_pos.2 (hm _ hlt)) Finset.univ_nonempty).ne' h1
    · exact hneg _ (fun t => sub_neg.2 (hm _ hlt)) h1
  · intro e
    have hc : Continuous (ψ i * (ψ j * ε)⁻¹) := (hO i).cont.mul ((hO j).cont.mul hεc).inv
    have hab : ∀ s : Weil h, ι.symm (absPow (w.adicCompletion L) 1 (a s)) = ((normV w : ℕ) : Qbar l) ^ deg s := fun s => by
      have := DFunLike.congr_fun (ha.absPow_comp 1) s
      rw [Complex.ofReal_one] at this
      rw [← MonoidHom.comp_apply, this, GlobalTheory.WeilDeligne.unrChar_apply, Units.val_zpow_eq_zpow_val, map_zpow₀]
      simp
    have hx : ∀ s : Weil h, (((ψ i * (ψ j * ε)⁻¹) (inc s) : (Qbar l)ˣ) : Qbar l) =
        algPow w (hh j - hh i - 1) (a s : w.adicCompletion L) := fun s => by
      rw [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.mul_inv_eq_iff_eq_mul, MonoidHom.mul_apply,
        Units.val_mul, hv, hv, hε, e, MonoidHom.mul_apply, Units.val_mul, map_mul, hab,
        show -hh i = (hh j - hh i - 1) + (-hh j + 1) by ring, algPow_add, algPow_add]
      ring
    have h1 := sum_zero ha _ _ hc hx
    rcases lt_or_gt_of_ne hij with hlt | hlt
    · have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun t _ => by
        have := hm (t.1.comp (algebraMap L _)) hlt
        simp only [Pi.sub_apply, Pi.one_apply] at this ⊢
        omega).1 h1
      refine hne i j (mul_inv_eq_one.1 (MonoidHom.ext fun g => Units.ext ?_))
      refine congrFun ((UpperTheory.weil_group_dense_in_galois_group L Ω w A h).equalizer (Units.continuous_val.comp hc) continuous_const
        (funext fun s => ?_)) g
      refine (hx s).trans (finprod_eq_one_of_forall_eq_one fun t => ?_)
      rw [h2 t (Finset.mem_univ _), zpow_zero]
    · refine hneg _ (fun t => ?_) h1
      have := hm (t.1.comp (algebraMap L _)) hlt
      simp only [Pi.sub_apply, Pi.one_apply] at this ⊢
      omega

theorem emb_place (j : W.Emb l w) (x : 𝓞 L) : ‖j.1.comp (algebraMap L _) (x : L)‖ < 1 ↔ x ∈ w.asIdeal := by
  have h1 : w.asIdeal ≤ (GlobalTheory.EvExtend.placeOf (j.1.comp (algebraMap L _))).asIdeal := fun y hy => by
    rw [GlobalTheory.EvExtend.mem_placeOf, ← tendsto_pow_atTop_nhds_zero_iff_norm_lt_one]
    have h2 : Valued.v (algebraMap L (w.adicCompletion L) (y : L)) < 1 := by
      rw [show Valued.v (algebraMap L (w.adicCompletion L) (y : L)) = w.valuation L (algebraMap (𝓞 L) L y) from
        HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _]
      exact (HeightOneSpectrum.valuation_lt_one_iff_mem w _).2 hy
    have h3 := (j.2.tendsto 0).comp (Valued.tendsto_zero_pow_of_v_lt_one h2)
    simpa [Function.comp_def] using h3
  rw [w.isMaximal.eq_of_le (GlobalTheory.EvExtend.placeOf _).isPrime.ne_top h1, GlobalTheory.EvExtend.mem_placeOf]

theorem jumps_eq (h : IsPlaceOver A w) (hw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal) {n : ℕ} {ι : Qbar l ≃+* ℂ} {r : Dec (F := L) A →* GL (Fin n) (Qbar l)}
    {J J' : (L →+* Qbar l) → Multiset ℤ} {P P' : Weil h → ℂ[X]} (H : DRat ι h r J P) (H' : DRat ι h r J' P')
    (j : W.Emb l w) : J (j.1.comp (algebraMap L _)) = J' (j.1.comp (algebraMap L _)) := by
  obtain ⟨O, _, _, _, Bw, hj⟩ := Af.exists_bridge (l := l) h hw
  obtain ⟨τ', hτ'⟩ := GlobalTheory.CharAboveRead.exists_isInduced_of _ w hw (emb_place j) A h O Bw hj
  obtain ⟨LL, r', hM, -, τ₁, hτ₁, hc⟩ := (H O Bw hj).2.1 _ _ _ hτ'
  ext k
  exact_mod_cast (hc k).trans (GlobalTheory.Pst.IsJumpsAt.count_eq _ hM hτ₁ ((H' O Bw hj).2.1 _ _ _ hτ') k).symm

theorem ord_div {ι : Qbar l ≃+* ℂ} {ω ω' : (w.adicCompletion L)ˣ →* ℂˣ} {d e : (L →+* Qbar l) → ℤ}
    {ψ ψ' : Dec (F := L) A →* (Qbar l)ˣ} (H : OrdChar ι a ω d ψ) (H' : OrdChar ι a ω' e ψ') :
    OrdChar ι a (ω / ω') (d - e) (ψ / ψ') := by
  refine ⟨?_, ?_, fun s g hg _ => ?_⟩
  · rw [div_eq_mul_inv]
    exact H.smooth.mul H'.smooth.inv
  · rw [div_eq_mul_inv]
    exact H.cont.mul H'.cont.inv
  · have h1 := H.val s g hg (Set.mem_univ _)
    have h2 := H'.val s g hg (Set.mem_univ _)
    simp only [MonoidHom.comp_apply, Units.coeHom_apply] at h1 h2 ⊢
    have h3 := algPow_add (w := w) (l := l) (-(d - e)) (-e) (a s)
    rw [show -(d - e) + -e = -d by abel] at h3
    rw [h3] at h1
    have h4 : ι.symm ((ω' (a s) : ℂˣ) : ℂ) ≠ 0 := (_root_.map_ne_zero _).2 (Units.ne_zero _)
    have h5 : ((ψ' g : (Qbar l)ˣ) : Qbar l) ≠ 0 := Units.ne_zero _
    have h6 : algPow w (-e) ((a s : (w.adicCompletion L)ˣ) : w.adicCompletion L) ≠ 0 := by
      rw [h2] at h5
      exact right_ne_zero_of_mul h5
    rw [MonoidHom.div_apply, MonoidHom.div_apply, Units.val_div_eq_div_val, Units.val_div_eq_div_val, map_div₀, h1, h2]
    field_simp

end

end

end UpperTheory.V.Z.Sym.AboveWeight

end
