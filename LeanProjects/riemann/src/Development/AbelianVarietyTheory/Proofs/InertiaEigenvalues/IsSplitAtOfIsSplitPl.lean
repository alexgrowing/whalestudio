import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.UnramBridgeHolds
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseChangeDistinctness
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOfNodupSumMultisetOfEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DualIsoDetGenMNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostCmData

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.BasicNotions Formalism.MainNotions.N

namespace GlobalTheory.DefiniteBC

section Weight

open GlobalTheory.Branching GlobalTheory.ValCmp

theorem exists_equiv_dual {m : ℕ} (lam : DomWeight (m + 1)) :
    ∃ κ : nablaSq ℂ (m + 1) lam ≃ₗ[ℂ] nablaSq ℂ (m + 1) lam.dual, ∀ g f,
      κ (sqRep ℂ (m + 1) lam g f) = sqRep ℂ (m + 1) lam.dual (inside₂ ℂ (m + 1) g) (κ f) := by
  obtain ⟨ha, hs, hl⟩ := factNatW (m + 1) lam
  have hl' : lam.natW (Fin.last m) = 0 := hl (Nat.succ_pos m)
  have h0 : lam.dual.detShift = -(lam.detShift + lam.natW 0 + 0) := by
    have := hs 0
    have e : lam.dual.detShift = -lam.w 0 := by
      simp only [DomWeight.detShift, Nat.succ_pos, dif_pos, DomWeight.dual]
      congr 2
      ext
      simp [Fin.val_rev]
    omega
  have hd : lam.dual.natW = nuDual lam.natW := by
    funext i
    have h1 := hs i.rev
    have h2 := hs 0
    have h3 : lam.dual.w i = -lam.w i.rev := rfl
    have h4 := ha (Fin.zero_le i.rev)
    simp only [nuDual]
    rw [DomWeight.natW]
    omega
  obtain ⟨Ψ, h1, h2, h3, -⟩ := exists_posOk_dual ℂ ℂ m lam.natW ha hl' lam.detShift 0
  rw [← hd] at h2
  have hm : ∀ f ∈ nablaSq ℂ (m + 1) lam, Ψ f ∈ nablaSq ℂ (m + 1) lam.dual := fun f hf => by
    unfold nablaSq
    rw [← h2]
    exact ⟨f, hf, rfl⟩
  refine ⟨LinearEquiv.ofBijective (Ψ.restrict hm) ⟨(injective_iff_map_eq_zero _).2 fun f hf =>
    Subtype.ext (h1 f f.2 (congrArg Subtype.val hf)), fun g => ?_⟩, fun g f => Subtype.ext ?_⟩
  · have hg : g.1 ∈ (Formalism.GradedWeylDivisibility.dualWeyl ℂ (m + 1) (m + 1) lam.natW).map Ψ := h2 ▸ g.2
    obtain ⟨f, hf, e⟩ := hg
    exact ⟨⟨f, hf⟩, Subtype.ext e⟩
  · have key : ∀ (mu : DomWeight (m + 1)) (x : GL (Fin (m + 1)) ℂ) (p),
        rnd ℂ mu.detShift (x.val⁻¹)ᵀ p = sqAct ℂ (m + 1) mu x p := fun mu x p => by
      have hx : IsUnit x.val.det := (Matrix.isUnit_iff_isUnit_det _).1 x.isUnit
      simp only [rnd, sqAct, detPow, LinearMap.smul_apply, AlgHom.toLinearMap_apply]
      rw [← Matrix.transpose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv _ hx, Matrix.det_transpose,
        Matrix.det_nonsing_inv, Ring.inverse_eq_inv', _root_.inv_zpow', neg_neg, Units.val_zpow_eq_zpow_val,
        GeneralLinearGroup.val_det_apply]
    have hx : IsUnit ((g.val⁻¹)ᵀ).det := by
      rw [Matrix.det_transpose]
      exact Matrix.isUnit_nonsing_inv_det _ ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit)
    have h4 := h3 _ hx f f.2
    rw [key, zpow_zero, one_smul, ← h0] at h4
    change Ψ (sqAct ℂ (m + 1) lam g f) = sqAct ℂ (m + 1) lam.dual (inside₂ ℂ (m + 1) g) (Ψ f)
    rw [h4, ← key]
    simp [inside₂]

theorem invTr_invTr {n : ℕ} (g : GL (Fin n) ℂ) : inside₂ ℂ n (inside₂ ℂ n g) = g :=
  Units.ext (Matrix.transpose_transpose _)

theorem infOfWeight_dual {n : ℕ} (lam : DomWeight n) :
    infOfWeight lam.dual = (infOfWeight lam).map (fun z => -z) := by
  unfold infOfWeight
  rw [Multiset.map_map]
  conv_rhs => rw [← Multiset.map_univ_val_equiv (Fin.revPerm : Equiv.Perm (Fin n)), Multiset.map_map]
  refine Multiset.map_congr rfl fun k _ => ?_
  have hk : ((k.rev : ℕ) : ℂ) = n - (k + 1) := by
    rw [Fin.val_rev, Nat.cast_sub (Nat.succ_le_of_lt k.2)]
    push_cast
    rfl
  simp only [DomWeight.dual, Function.comp_apply, Fin.revPerm_apply, hk]
  push_cast
  ring

theorem nodup_infOfWeight {n : ℕ} (lam : DomWeight n) : (infOfWeight lam).Nodup := by
  refine Finset.univ.nodup.map fun i j h => ?_
  have h1 : lam.w i - (i : ℕ) = lam.w j - (j : ℕ) := by
    have : ((lam.w i - (i : ℕ) : ℤ) : ℂ) = ((lam.w j - (j : ℕ) : ℤ) : ℂ) := by
      push_cast
      linear_combination h
    exact_mod_cast this
  rcases lt_trichotomy i j with h | h | h
  · have := lam.anti h.le
    have : (i : ℕ) < j := h
    omega
  · exact h
  · have := lam.anti h.le
    have : (j : ℕ) < i := h
    omega

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem coord_conjugate (τ : E →+* ℂ) (z : Cinf E) :
    coord (ComplexEmbedding.conjugate τ) z = starRingEnd ℂ (coord τ z) := by
  have hne : ComplexEmbedding.conjugate τ ≠ τ := fun h =>
    InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk τ))
      (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 h))
  unfold coord
  simp only [InfinitePlace.mk_conjugate_eq]
  rcases InfinitePlace.embedding_mk_eq τ with h | h
  · rw [if_pos h, if_neg (by rw [InfinitePlace.mk_conjugate_eq, h]; exact hne.symm)]
    rfl
  · rw [if_pos (by rw [InfinitePlace.mk_conjugate_eq, h]), if_neg (by rw [h]; exact hne)]
    simp

theorem coord_conjAd (τ : E →+* ℂ) (x : Ad E) :
    coord τ (pInf E (conjAd E x)) = starRingEnd ℂ (coord τ (pInf E x)) := by
  have e : pInf E (conjAd E x) = star (pInf E x) := (infEq E).symm_apply_apply _
  rw [e]
  unfold coord
  split_ifs <;> simp

theorem cEmb_conjugate (τ : E →+* ℂ) (x : UA E n) :
    cEmb (ComplexEmbedding.conjugate τ) x = inside₂ ℂ n (cEmb τ x) := by
  have hx : Formalism.UG.cT (conjAd E) x.1.val * 1 * x.1.val = 1 := x.2
  have h1 := congrArg (RingHom.mapMatrix ((coord τ).comp (pInf E))) hx
  rw [mul_one, map_mul, map_one] at h1
  have h2 : (cEmb (ComplexEmbedding.conjugate τ) x).valᵀ * (cEmb τ x).val = 1 := by
    rw [← h1]
    congr 1
    ext i j
    exact (coord_conjugate τ _).trans (coord_conjAd τ _).symm
  apply Units.ext
  change _ = ((cEmb τ x)⁻¹).valᵀ
  rw [Matrix.coe_units_inv, Matrix.inv_eq_left_inv h2, Matrix.transpose_transpose]

theorem embU_conjugate (τ : E →+* ℂ) : embU n (ComplexEmbedding.conjugate τ) = embU n τ := by
  simp only [embU, InfinitePlace.mk_conjugate_eq]

theorem hasWeightAt_conjugate (hn : 1 ≤ n) {π : Submodule ℂ (UA E n → ℂ)} {τ : E →+* ℂ} {lam : DomWeight n}
    (h : HasWeightAt π τ lam) : HasWeightAt π (ComplexEmbedding.conjugate τ) lam.dual := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨κ, hκ⟩ := exists_equiv_dual lam
  obtain ⟨hi, f, h0, h1, h2⟩ := h
  refine ⟨(GlobalTheory.SmGL.MultiIrr.isIrreducible_iff_of_linearEquiv _ (fun g => ⟨_, invTr_invTr g⟩) κ hκ).1 hi,
    f ∘ₗ κ.symm.toLinearMap, fun e => h0 (LinearMap.ext fun v => ?_), fun v => h1 _, fun x v => ?_⟩
  · simpa using LinearMap.congr_fun e (κ v)
  · obtain ⟨v, rfl⟩ := κ.surjective v
    change f (κ.symm (sqRep ℂ _ _ (cEmb (ComplexEmbedding.conjugate τ) x.1) (κ v))) = RU E _ x (f (κ.symm (κ v)))
    rw [cEmb_conjugate, ← hκ, κ.symm_apply_apply, κ.symm_apply_apply]
    exact h2 ⟨x.1, embU_conjugate τ ▸ x.2⟩ v

end Weight

section Discrete

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E]

abbrev LocIrr (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) : Type 1 := SmIrr (GL (Fin n) (w.adicCompletion E))

def spehInd {a d N : ℕ} (h : ∑ _ : Fin d, a = N) {w : HeightOneSpectrum (𝓞 E)} (σ : LocIrr w a) :=
  GlobalTheory.SmGL.multiProd (GlobalTheory.SmGL.stdBlocks (fun _ : Fin d => a) h) fun k =>
    GlobalTheory.SmGL.twist σ.ρ (GlobalTheory.SmGL.detChar (Fin a) (GlobalTheory.SmGL.absPow (w.adicCompletion E) (((d : ℂ) - 1) / 2 - (k : ℕ))))

def IsSpehQuot {a d N : ℕ} (h : ∑ _ : Fin d, a = N) {w : HeightOneSpectrum (𝓞 E)} (σ : LocIrr w a)
    (σ' : LocIrr w N) : Prop :=
  ∃ f : (spehInd h σ).IntertwiningMap σ'.ρ, Function.Surjective f

def spehInf (d : ℕ) (m : Multiset ℂ) : Multiset ℂ :=
  ((List.range d).map fun k : ℕ => m.map (· + (((d : ℂ) - 1) / 2 - k))).sum

variable (E) in

def DiscreteSpectrum [IsCMField E] : Prop :=
  ∀ N : ℕ, 1 ≤ N → ∀ V : Submodule ℂ (Sm E N), IsDiscrete V →
    ∃ (a d : ℕ) (h : ∑ _ : Fin d, a = N) (P : CuspSub E a), (IsCsdGL V → P.IsCsd) ∧
      (∀ w σ', IsLocCompGL V w σ' → GlobalTheory.SmGL.IsUnitarisable σ'.ρ ∧
        ∃ σ, P.IsLocComp w σ ∧ GlobalTheory.SmGL.IsUnitarisable σ.ρ ∧ IsSpehQuot h σ σ') ∧
      ∀ τ m', HasInfCharGL V τ m' → ∃ m, P.HasInfChar τ m ∧ m' = spehInf d m

end Discrete

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂}

attribute [local instance] host_isCMField

abbrev RecMap (A : NAut N) : Type 1 := ∀ (w : PlE H) (n : ℕ), LocIrr w n → A.LP w

variable {A : NAut N}

def lpSumList {w : PlE H} (L : List (A.LP w)) : A.LP w := L.foldr A.lpSum (A.lpZero w)

def RecProd (rc : RecMap A) : Prop :=
  ∀ (w : PlE H) (c n : ℕ) (d : Fin c → ℕ) (h : ∑ i, d i = n) (σ : ∀ i, LocIrr w (d i)) (σ' : LocIrr w n),
    Nonempty (σ'.ρ.Equiv (locProd h w σ)) → rc w n σ' = lpSumList (List.ofFn fun i => rc w (d i) (σ i))

def RecSpeh (rc : RecMap A) : Prop :=
  ∀ (w : PlE H) (a d n : ℕ) (h : ∑ _ : Fin d, a = n) (P : CuspSub H.E a) (σ : LocIrr w a) (σ' : LocIrr w n),
    P.IsLocComp w σ → GlobalTheory.SmGL.IsUnitarisable σ.ρ → IsSpehQuot h σ σ' →
    rc w n σ' = lpSumList ((List.range d).map fun k : ℕ => A.lpTw (rc w a σ) (((d : ℝ) - 1) / 2 - k))

def RecSatake (rc : RecMap A) : Prop :=
  ∀ (w : PlE H) (n : ℕ) (σ : LocIrr w n) (S : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w σ.ρ S →
    A.unr (rc w n σ) ∧ A.frobEig (rc w n σ) = S.map fun z => ((z⁻¹ : ℂˣ) : ℂ)

def CuspRead (rc : RecMap A) : Prop :=
  ∀ (a : ℕ) (P : CuspSub H.E a), 1 ≤ a → P.IsCsd → ∃ π : A.CG a, A.csd π ∧
    (∀ w σ, P.IsLocComp w σ → A.locG π w = rc w a σ) ∧ ∀ τ m, P.HasInfChar τ m → A.infG π τ = m

def IsSatAt {n : ℕ} (U : Submodule ℂ (UA H.E n → ℂ)) (w : PlE H) (α : Fin (n / 2) → ℂˣ) : Prop :=
  ∃ (s : w.adicCompletion H.E →+* w.adicCompletion H.E) (ϖ : w.adicCompletion H.E) (q : ℕ),
    (∀ x : H.E, s (algebraMap H.E _ x) = algebraMap H.E _ (IsCMField.complexConj H.E x)) ∧
      Formalism.UG.IsUnramInv ϖ s q ∧ HasSatAt U w s ϖ q α

def UnitaryRead (B : NBC A) (rc : RecMap A) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ R.m → ∀ π : B.AU j, ∃ U : Submodule ℂ (UA H.E R.nV → ℂ), IsAutRepU U ∧
    (∀ w : PlE H, IsSplitPl H w → ∀ σ : LocIrr w R.nV,
      IsCompAlong U (locU R.nV w) ((cLoc w).comp (locU R.nV w).subtype) σ.ρ → B.locAU j π w = rc w R.nV σ) ∧
    (∀ w : PlE H, ¬ IsSplitPl H w → B.sphAU j π w →
      ∃ α, IsSatAt U w α ∧ B.satAU j π w = Finset.univ.val.map fun i => (α i : ℂ)) ∧
    ∀ τ : H.E →+* ℂ, ∃ lam, HasWeightAt U τ lam ∧ B.infW j (B.wtAU j π) τ = infOfWeight lam

theorem host_unramified (H : Host R) (w : PlE H) :
    Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield H.E)) w.asIdeal := by
  have h : Algebra.Unramified (𝓞 (maximalRealSubfield H.E)) (𝓞 H.E) :=
    Formalism.L2.Pj.unramBridge_holds H.E fun P hP => by
      letI := H.cmStar
      obtain ⟨θ, t, e1, e2⟩ := (GlobalTheory.Mem.host_cmData R H).cmUnram.2.2 P hP
      refine ⟨θ, ?_⟩
      have : RingOfIntegers.mapRingEquiv (IsCMField.complexConj H.E : H.E ≃+* H.E) θ = t :=
        RingOfIntegers.ext e1.symm
      rwa [this]
  exact Algebra.unramified_iff_forall.1 h ⟨w.asIdeal, w.isPrime⟩

theorem isSplitAt_of_isSplitPl {w : PlE H} (h : IsSplitPl H w) : IsSplitAt w := by
  obtain ⟨x, hx, hy⟩ := h
  let c := IsCMField.ringOfIntegersComplexConj H.E
  refine ⟨w.comap c.toRingEquiv.toRingHom c.surjective, fun e => hy (c x) (host_complexConj H x) ?_,
    HeightOneSpectrum.ext (Ideal.ext fun y => ?_)⟩
  · rw [← e] at hx
    exact hx
  · change c (algebraMap _ _ y) ∈ w.asIdeal ↔ algebraMap _ _ y ∈ w.asIdeal
    rw [c.commutes]

theorem ubc_eq_map_inv (n : ℕ) (α : Fin (n / 2) → ℂˣ) :
    ((GlobalTheory.LGrp.bcParam n α).map fun z => ((z⁻¹ : ℂˣ) : ℂ)) = ubc n (Finset.univ.val.map fun i => (α i : ℂ)) := by
  unfold GlobalTheory.LGrp.bcParam ubc
  simp only [Multiset.map_add, Multiset.map_map, Function.comp_def, inv_inv, Units.val_inv_eq_inv_val]
  rw [add_comm (Multiset.map (fun i => ((α i : ℂ))⁻¹) _)]
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h, Nat.odd_iff]

theorem spehLoc_eq (p : Part A.CG) (w : PlE H) : spehLoc N A p w =
    lpSumList ((List.range p.d).map fun k : ℕ => A.lpTw (A.locG p.π w) (((p.d : ℝ) - 1) / 2 - k)) := by
  simp only [spehLoc, lpSumList, bind_pure_comp, List.map_eq_map, List.foldr_map]

theorem isoInf_eq (Pa : List (Part A.CG)) (τ : H.E →+* ℂ) :
    isoInf N A Pa τ = (Pa.map fun p => spehInf p.d (A.infG p.π τ)).sum := by
  simp only [isoInf, spehInf, bind_pure_comp, List.map_eq_map, List.map_map, Function.comp_def]

theorem exists_part {rc : RecMap A} (hMW : DiscreteSpectrum H.E) (hS : RecSpeh rc) (hC : CuspRead rc) {n : ℕ}
    (hn : 0 < n) {V : Submodule ℂ (Sm H.E n)} (hV : IsDiscrete V) (hc : IsCsdGL V) :
    ∃ p : Part A.CG, 1 ≤ p.a ∧ 1 ≤ p.d ∧ A.csd p.π ∧ p.a * p.d = n ∧
      (∀ w σ, IsLocCompGL V w σ → GlobalTheory.SmGL.IsUnitarisable σ.ρ ∧ rc w n σ = spehLoc N A p w) ∧
      ∀ τ m, HasInfCharGL V τ m → m = spehInf p.d (A.infG p.π τ) := by
  obtain ⟨a, d, h, P, h1, h2, h3⟩ := hMW n hn V hV
  have had : a * d = n := by simpa [mul_comm] using h
  have ha : 1 ≤ a := Nat.pos_of_mul_pos_right (had ▸ hn)
  obtain ⟨π, c1, c2, c3⟩ := hC a P ha (h1 hc)
  refine ⟨⟨a, π, d⟩, ha, Nat.pos_of_mul_pos_left (had ▸ hn), c1, had, fun w σ' hσ' => ?_, fun τ m' hm' => ?_⟩
  · obtain ⟨u, σ, l, u', q⟩ := h2 w σ' hσ'
    refine ⟨u, ?_⟩
    rw [hS w a d n h P σ σ' l u' q, ← c2 w σ l, spehLoc_eq]
  · obtain ⟨m, hm, rfl⟩ := h3 τ m' hm'
    rw [c3 τ m hm]

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField in

theorem exists_parts {rc : RecMap A} (hNT : GlobalTheory.Published.BaseChangeDefiniteUnitary)
    (hB : GlobalTheory.Published.BernsteinUnitaryProductIrreducible) (hMW : DiscreteSpectrum H.E)
    (hP : RecProd rc) (hS : RecSpeh rc) (hSat : RecSatake rc) (hC : CuspRead rc)
    {n : ℕ} (hn : 1 ≤ n) {U : Submodule ℂ (UA H.E n → ℂ)} (hU : IsAutRepU U) :
    ∃ Pa : List (Part A.CG), (∀ p ∈ Pa, 1 ≤ p.a ∧ 1 ≤ p.d ∧ A.csd p.π) ∧ rankIso N A Pa = n ∧
      (∀ w, IsSplitPl H w → ∃ σ : LocIrr w n,
        IsCompAlong U (locU n w) ((cLoc w).comp (locU n w).subtype) σ.ρ ∧ isoLoc N A Pa w = rc w n σ) ∧
      (∀ w α, IsSatAt U w α → A.unr (isoLoc N A Pa w) ∧
        A.frobEig (isoLoc N A Pa w) = ubc n (Finset.univ.val.map fun i => (α i : ℂ))) ∧
      ∀ τ lam, HasWeightAt U τ lam → Pa.Nodup ∧ isoInf N A Pa τ = infOfWeight lam ∧
        isoInf N A Pa (ComplexEmbedding.conjugate τ) = (infOfWeight lam).map (fun z => -z) := by
  obtain ⟨c, d, h, V, σ, m, bc⟩ := hNT H.E (host_unramified H) n hn U hU
  choose p p1 p2 p3 p4 p5 p6 using fun i => exists_part hMW hS hC (bc.pos i) (bc.discrete i) (bc.csd i)
  let Q : ∀ w, LocIrr w n := fun w =>
    { V := _
      ρ := locProd h w (σ · w)
      smooth := GlobalTheory.SmGL.isSmooth_parInd _ _
      irred := GlobalTheory.SmGL.MultiIrr.isIrreducible_multiProd hB _ (fun i => (σ i w).smooth) (fun i => (σ i w).irred)
        fun i => (p5 i w _ (bc.loc i w)).1 }
  have hloc : ∀ w, isoLoc N A (List.ofFn p) w = rc w n (Q w) := fun w => by
    rw [hP w c n d h (σ · w) (Q w) ⟨.refl _⟩]
    simp only [fun i => (p5 i w _ (bc.loc i w)).2]
    rw [lpSumList, ← Function.comp_def (fun q => spehLoc N A q w) p, ← List.map_ofFn, List.foldr_map]
    rfl
  have hinf : ∀ τ, isoInf N A (List.ofFn p) τ = ∑ i, m i τ := fun τ => by
    rw [isoInf_eq, List.map_ofFn, List.sum_ofFn]
    exact Finset.sum_congr rfl fun i _ => (p6 i τ _ (bc.inf i τ)).symm
  refine ⟨List.ofFn p, fun q hq => ?_, ?_, fun w hw => ⟨Q w, bc.split w (isSplitAt_of_isSplitPl hw), hloc w⟩,
    fun w α ⟨s, ϖ, q, e1, e2, e3⟩ => ?_, fun τ lam hl => ⟨List.nodup_ofFn.2 fun i j e => ?_, ?_, ?_⟩⟩
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hq
    exact ⟨p1 i, p2 i, p3 i⟩
  · rw [rankIso, List.map_ofFn, List.sum_ofFn, ← h]
    exact Finset.sum_congr rfl fun i _ => p4 i
  · rw [hloc, ← ubc_eq_map_inv]
    exact hSat w n (Q w) _ (bc.inert w s ϖ q e1 e2 α e3)
  · refine GlobalTheory.eq_of_nodup_sum_multiset_of_eq (Fin c) (m · τ) (bc.weight τ lam hl ▸ nodup_infOfWeight lam) i j
      (fun h0 => (bc.pos i).ne' ?_) ?_
    · rw [← (bc.inf i τ).1]
      exact Multiset.card_eq_zero.2 h0
    · change m i τ = m j τ
      rw [p6 i τ _ (bc.inf i τ), p6 j τ _ (bc.inf j τ), e]
  · rw [hinf, bc.weight τ lam hl]
  · rw [hinf, bc.weight _ _ (hasWeightAt_conjugate hn hl), infOfWeight_dual]

theorem baseChangeDefinite_at (B : NBC A) (rc : RecMap A) (hNT : GlobalTheory.Published.BaseChangeDefiniteUnitary)
    (hB : GlobalTheory.Published.BernsteinUnitaryProductIrreducible) (hMW : DiscreteSpectrum H.E)
    (hP : RecProd rc) (hS : RecSpeh rc) (hSat : RecSatake rc) (hC : CuspRead rc) (hU : UnitaryRead B rc) :
    GlobalTheory.IndefiniteRowSideFullHecke.BaseChangeDistinctness.BaseChangeDefinite_at B := by
  intro j h1 h2 π hπ
  obtain ⟨U, u1, u2, u3, u4⟩ := hU j h1 h2 π
  have hn : 1 ≤ R.nV := by
    have := R.rank_add_five_le
    simp only [Ranks.nV]
    omega
  obtain ⟨Pa, a1, a2, a3, a4, a5⟩ := exists_parts hNT hB hMW hP hS hSat hC hn u1
  refine ⟨Pa, fun p hp => ⟨(a1 p hp).1, (a1 p hp).2.1⟩, fun p hp => (a1 p hp).2.2, ?_, a2, fun w hw => ?_,
    fun w hw => ?_, fun τ => ?_, fun τ _ => ?_⟩
  · obtain ⟨lam, hl, -⟩ := u4 H.φ₀
    exact (a5 _ lam hl).1
  · obtain ⟨σ, s1, s2⟩ := a3 w hw
    rw [s2, u2 w hw σ s1]
  · obtain ⟨α, s1, s2⟩ := u3 w hw (hπ w hw)
    rw [s2]
    exact a4 w α s1
  · obtain ⟨lam, hl, e⟩ := u4 τ
    rw [e, (a5 τ lam hl).2.1]
  · obtain ⟨lam, hl, e⟩ := u4 τ
    rw [e, (a5 τ lam hl).2.2]

end GlobalTheory.DefiniteBC

end
