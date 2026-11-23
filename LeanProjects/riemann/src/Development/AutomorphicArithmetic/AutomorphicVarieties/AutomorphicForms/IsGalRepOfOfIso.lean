import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SatOfFixed
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.GlobFixed
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterInvariantUnderConjugation

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
open TensorProduct Module GlobalTheory.CoeffExt
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Af.ExLib

theorem eventually_sat (hS : SatLoc) {F : Type} [Field F] [NumberField F] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin n) (Af F)) V) (hρ : GlobalTheory.PRep.IsSmooth ρ) (h : ∀ w, ∃ σ, LocIsotypic ρ w σ) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ B, GlobalTheory.LFun.HasSatGL w (ρ.comp (locGL F n w)) B := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · refine .of_forall fun w => ?_
    obtain ⟨σ, hσ, -⟩ := h w
    exact absurd hσ (not_nontrivial V)
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨S, hU⟩ := GlobalFixedVectors.exists_KAway_subset (M := 1) ((hρ v).mem_nhds (by simp))
  filter_upwards [S.eventually_cofinite_notMem] with w hw
  obtain ⟨σ, hi⟩ := h w
  obtain ⟨h1, h2⟩ := hS F n w σ
  have hK : IsCompact (GlobalTheory.LFun.KGL w n : Set (GL (Fin n) (w.adicCompletion F))) :=
    GlobalTheory.LFun.IntPtsUnitary.isCompact_GLint _ (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F w)
  have h0 : ((1 : ℕ) : 𝓞 F) ∉ w.asIdeal := by
    rw [Nat.cast_one]; exact (Ideal.ne_top_iff_one _).1 w.isPrime.ne_top
  obtain ⟨B, hB⟩ := h1 (hasFixed_of_sum σ.ρ σ.smooth (ρ.comp (locGL F n w)) _ hK hi.2
    ⟨v, hv, fun u hu => hU (GlobalFixedVectors.mem_KAway.2 ⟨locGL_mem_KLev n w h0 hu, fun x hx =>
      pLoc_locGL_of_ne (show x ≠ w from fun e => hw (e ▸ hx)) _⟩)⟩)
  exact ⟨B, (h2 _ _ hi B).2 hB⟩

section Coord

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K L L' : FinExt l}
  {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V]
  {V' : Type} [AddCommGroup V'] [Module ↥L.1 V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] ↥L.1 V']
  [Module ↥L'.1 V'] [IsScalarTower ℚ_[l] ↥L'.1 V']
  {ρ : Representation ↥L.1 ↥(GK K) V} {ρ' : Representation ↥L'.1 ↥(GK K) V'}
  {ι : Type} [Fintype ι] [DecidableEq ι] {E : V' ≃ₗ[↥L.1] (ι → V)}

theorem isSst_iff : IsSst P ρ ↔ finrank ℚ_[l] ↥(Dst P ρ) = finrank ℚ_[l] ↥(K0 K) * finrank ℚ_[l] V := by
  have := L.2
  rw [IsSst, ← finrank_mul_finrank ℚ_[l] ↥L.1 V, ← finrank_mul_finrank ℚ_[l] ↥L.1 ↥(Dst P ρ), mul_left_comm]
  exact (Nat.mul_right_inj finrank_pos.ne').symm

private theorem finrank_fun' {k M ι : Type} [Field k] [AddCommGroup M] [Module k M] [Fintype ι] :
    finrank k (ι → M) = Fintype.card ι * finrank k M := by
  rw [finrank, rank_fun, Cardinal.toNat_mul, Cardinal.toNat_natCast, finrank]

theorem isSst_of_coord (hE : ∀ g x i, E (ρ' g x) i = ρ g (E x i)) (h : IsSst P ρ) : IsSst P ρ' := by
  have hm : ∀ x : V' ⊗[ℚ_[l]] Bst P, x ∈ Dst P ρ' ↔ ∀ i, tensCoord E (Bst P) x i ∈ Dst P ρ := fun x => by
    simp only [mem_Dst]
    refine ⟨fun hx i g => by rw [← GlobalTheory.PstExt.tensCoord_stRep P hE, hx g], fun hx g => ?_⟩
    exact (tensCoord E (Bst P)).injective (funext fun i => by rw [GlobalTheory.PstExt.tensCoord_stRep P hE, hx i g])
  let e : ↥(Dst P ρ') ≃ₗ[ℚ_[l]] (ι → ↥(Dst P ρ)) :=
    { toFun := fun x i => ⟨tensCoord E (Bst P) x.1 i, (hm _).1 x.2 i⟩
      invFun := fun y => ⟨(tensCoord E (Bst P)).symm fun i => (y i).1, (hm _).2 fun i => by
        rw [LinearEquiv.apply_symm_apply]; exact (y i).2⟩
      map_add' := fun x y => funext fun i => Subtype.ext (congrFun (map_add (tensCoord E (Bst P)) x.1 y.1) i)
      map_smul' := fun c x => funext fun i =>
        Subtype.ext (congrFun (((tensCoord E (Bst P)).restrictScalars ℚ_[l]).map_smul c x.1) i)
      left_inv := fun x => Subtype.ext ((tensCoord E (Bst P)).symm_apply_apply x.1)
      right_inv := fun y => funext fun i =>
        Subtype.ext (congrFun ((tensCoord E (Bst P)).apply_symm_apply fun i => (y i).1) i) }
  rw [isSst_iff] at h ⊢
  rw [e.finrank_eq, (E.restrictScalars ℚ_[l]).finrank_eq, finrank_fun', finrank_fun', h, mul_left_comm]

end Coord

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] {m : ℕ}

theorem isSst_enlarge {Gw : Subgroup (Ω ≃ₐ[E] Ω)} (Bw : LocBridge l E Ω Gw O) {L₁ L₂ : FinExt l} (hL : L₁.1 ≤ L₂.1)
    (r₁ : ↥Gw →* GL (Fin m) ↥L₁.1) (h : IsSst P (Bw.repE L₁ r₁)) :
    IsSst P (Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁)) := by
  let _ : Algebra ↥L₁.1 ↥L₂.1 := (IntermediateField.inclusion hL).toRingHom.toAlgebra
  have : IsScalarTower ℚ_[l] ↥L₁.1 ↥L₂.1 := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := L₂.2
  have : FiniteDimensional ↥L₁.1 ↥L₂.1 := Module.Finite.of_restrictScalars_finite ℚ_[l] _ _
  have hρ : ∀ g, ∃ M : Matrix (Fin m) (Fin m) ↥L₁.1, (∀ x, Bw.repE L₁ r₁ g x = M.mulVec x) ∧
      ∀ x, Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁) g x =
        (M.map (algebraMap ↥L₁.1 ↥L₂.1)).mulVec x :=
    fun g => ⟨r₁ (Bw.e.symm g), fun _ => rfl, fun _ => rfl⟩
  exact isSst_of_coord P (E := vecCoord ↥L₁.1 ↥L₂.1 m) (vecCoord_rep hρ) h

theorem isSstAt_conj {Gw : Subgroup (Ω ≃ₐ[E] Ω)} (Bw : LocBridge l E Ω Gw O) {r r' : ↥Gw →* GL (Fin m) (Om l)}
    (p : GL (Fin m) (Om l)) (hc : ∀ g, r' g = p * r g * p⁻¹) (h : IsSstAt P Bw r) : IsSstAt P Bw r' := by
  obtain ⟨L₁, r₁, h₁, hp⟩ := h
  obtain ⟨L₂, hL, r₂, hm, e, he⟩ := GlobalTheory.ConjLocal.exists_conj_model p hc h₁
  refine ⟨L₂, r₂, hm, isSst_of_coord P (ι := Unit) (E := e.symm.trans (LinearEquiv.funUnique Unit _ _).symm)
    (fun g x _ => ?_) (isSst_enlarge P Bw hL r₁ hp)⟩
  change e.symm _ = Bw.repE L₂ _ g (e.symm x)
  rw [e.symm_apply_eq, he, e.apply_symm_apply]

theorem isPstAt_conj {Gw : Subgroup (Ω ≃ₐ[E] Ω)} (Bw : LocBridge l E Ω Gw O) {r r' : ↥Gw →* GL (Fin m) (Om l)}
    (p : GL (Fin m) (Om l)) (hc : ∀ g, r' g = p * r g * p⁻¹) (h : IsPstAt P Bw r) : IsPstAt P Bw r' := by
  obtain ⟨L₁, r₁, h₁, hp⟩ := h
  obtain ⟨L₂, hL, r₂, hm, e, he⟩ := GlobalTheory.ConjLocal.exists_conj_model p hc h₁
  exact ⟨L₂, r₂, hm, GlobalTheory.PstConj.isPst_congr P e he (GlobalTheory.PstExt.isPst_enlarge P Bw hL r₁ hp)⟩

theorem wdAt_conj [NumberField E] [IsAlgClosure E Ω] (ι : Om l ≃+* ℂ) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw)
    {r r' : ↥(Dec (F := E) A) →* GL (Fin m) (Om l)} (p : GL (Fin m) (Om l)) (hc : ∀ g, r' g = p * r g * p⁻¹) :
    wdAt P ι Bw h hj r' = wdAt P ι Bw h hj r := by
  by_cases hr : IsPstAt P Bw r
  · exact GlobalTheory.ConjGal.wdAt_conj P ι Bw h hj r r' p hc hr (isPstAt_conj P Bw p hc hr)
  · rw [wdAt_of_not_isPstAt ι Bw h hj hr, wdAt_of_not_isPstAt ι Bw h hj fun hr' =>
      hr (isPstAt_conj P Bw p⁻¹ (fun g => by rw [hc]; group) hr')]

theorem isConjDual_of_iso {k : Type} [Field k] {c : Ω ≃+* Ω} {r r' : G E Ω →* GL (Fin m) k} {μ : G E Ω →* kˣ}
    (H : IsConjDual c r μ) (h : RepIso r r') : IsConjDual c r' μ := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨Q, hQ⟩ := H
  let t : GL (Fin m) k := ⟨(g : Matrix (Fin m) (Fin m) k)ᵀ, ((g⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k)ᵀ,
    by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]⟩
  have ht : (t : Matrix (Fin m) (Fin m) k) = (g : Matrix (Fin m) (Fin m) k)ᵀ := rfl
  have ht' : ((t⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) = ((g⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k)ᵀ := rfl
  refine ⟨g * Q * t, fun s s' hs => ?_⟩
  rw [hg s', hg s⁻¹]
  simp only [Units.val_mul, mul_inv_rev, hQ s s' hs, Matrix.transpose_mul, ← ht, ← ht', Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_assoc, Units.mul_inv_cancel_left]

theorem isGalRepOf_of_iso [NumberField E] [IsAlgClosure E Ω] [IsCMField E] {π : CuspSub E m}
    {χ : HChar (maximalRealSubfield E)} {ι : Qbar l ≃+* ℂ} {r r' : G E Ω →* GL (Fin m) (Qbar l)} {wt : ℤ}
    {HT : (E →+* Qbar l) → Multiset ℤ} (H : IsGalRepOf π χ ι r wt HT) (hs : IsSSRep r') (h : RepIso r r') :
    IsGalRepOf π χ ι r' wt HT := by
  obtain ⟨μ, h1, h2⟩ := H.pol
  have hc := continuous_of_iso H.cont h
  have h3 := fun c hc => isConjDual_of_iso (h2 c hc) h
  obtain ⟨g, hg⟩ := h
  have hg' : ∀ s, g * r s = r' s * g := fun s => by rw [hg, inv_mul_cancel_right]
  refine ⟨hc, hs, ⟨μ, h1, h3⟩, fun w hw A h rc hrc σ hσ => (H.away w hw A h rc hrc σ hσ).of_conj hw g fun s => hg' _,
    fun w hw A h => (H.pure w hw A h).imp fun x hx => ⟨hx.1.of_conj hw g fun s => hg' _, hx.2⟩, H.weights, H.weights_conj,
    fun P AI T w A h O _ _ _ Bw hj => ?_⟩
  have Ha := H.above P AI T w A h O Bw hj
  have e : ∀ s : ↥(Dec (F := E) A), r'.comp (Dec (F := E) A).subtype s = g * r.comp (Dec (F := E) A).subtype s * g⁻¹ :=
    fun s => hg s
  obtain ⟨c1, c2, -, c4⟩ := GlobalTheory.T.padicHodgeProperties_conj_invariant l P E Ω O _ Bw m _ _ g e
  exact ⟨c1 Ha.deRham, fun τ L τ' hτ => c4 _ _ (Ha.jumps τ L τ' hτ), fun σ hσ hf =>
    ⟨isSstAt_conj P Bw g e (Ha.iwahori σ hσ hf).1, fun rc hrc =>
      (wdAt_conj P ι Bw h hj g e).trans ((Ha.iwahori σ hσ hf).2 rc hrc)⟩, fun σ hσ hf => c2 (Ha.crys σ hσ hf)⟩

end UpperTheory.V.Af.ExLib

end
