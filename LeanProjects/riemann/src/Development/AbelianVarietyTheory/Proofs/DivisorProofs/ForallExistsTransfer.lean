import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ISupIInfEigenspaceEqTop
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AdelicUnitarySupportedAtFinitePlaceEqLocalUnitar
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalMatrixDoubleCosetOfElementaryDivisors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactParahoricLevelAndContainsLifts
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MemConj

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField
open scoped TensorProduct Matrix

namespace GlobalTheory.HeckeLabels

section Abstract

theorem forall_exists_transfer {X X' Z Z' : Type} {L : X → Prop} {L' : X' → Prop} {I : Z → Prop} {I' : Z' → Prop}
    (p : X → X') (q : Z → Z') (p1 : ∀ y, L y → L' (p y)) (p2 : ∀ y', L' y' → ∃ y, L y ∧ p y = y')
    (q1 : ∀ z, I z → I' (q z)) (q2 : ∀ z', I' z' → ∃ z, I z ∧ q z = z') {P : X → Z → Prop} {P' : X' → Z' → Prop}
    (h : ∀ y z, P y z ↔ P' (p y) (q z)) :
    (∀ y, L y → ∃ z, I z ∧ P y z) ↔ ∀ y', L' y' → ∃ z', I' z' ∧ P' y' z' := by
  constructor
  · intro H y' hy'
    obtain ⟨y, hy, rfl⟩ := p2 y' hy'
    obtain ⟨z, hz, e⟩ := H y hy
    exact ⟨q z, q1 z hz, (h y z).1 e⟩
  · intro H y hy
    obtain ⟨z', hz', e⟩ := H _ (p1 y hy)
    obtain ⟨z, hz, rfl⟩ := q2 z' hz'
    exact ⟨z, hz, (h y z).2 e⟩

variable {R : Type} [CommRing R] {n : ℕ}

def StdDiv (O : Subring R) (ε : R) (t : Fin n → R) (m : Matrix (Fin n) (Fin n) R) : Prop :=
  ∃ B : Matrix (Fin n) (Fin n) R,
    (∀ z : Fin n → R, (∀ i, z i ∈ O) → ∀ i, (ε • B *ᵥ z) i ∈ O) ∧
    (∀ y : Fin n → R, (∀ i, y i ∈ O) → ∃ z : Fin n → R, (∀ i, z i ∈ O) ∧ ε • y = ε • B *ᵥ z) ∧
    (∀ y : Fin n → R, (∀ i, y i ∈ O) → ∃ z : Fin n → R, (∀ i, z i ∈ O) ∧ ε • m *ᵥ y = ε • B *ᵥ (t * z)) ∧
    (∀ z : Fin n → R, (∀ i, z i ∈ O) → ∃ y : Fin n → R, (∀ i, y i ∈ O) ∧ ε • m *ᵥ y = ε • B *ᵥ (t * z))

theorem conj_mem_UJ (σ : R →+* R) {J J' : Matrix (Fin n) (Fin n) R} {h : GL (Fin n) R}
    (hh : Formalism.UG.cT σ h.1 * J * h.1 = J') {g : GL (Fin n) R} (hg : g ∈ Formalism.UG.UJ σ J) :
    h⁻¹ * g * h ∈ Formalism.UG.UJ σ J' := by
  have hg' : Formalism.UG.cT σ g.1 * J * g.1 = J := hg
  show Formalism.UG.cT σ (h⁻¹ * g * h).1 * J' * (h⁻¹ * g * h).1 = J'
  have e : h.1 * (h⁻¹ * g * h).1 = g.1 * h.1 := by
    rw [← Units.val_mul, ← Units.val_mul]; congr 1; group
  calc _ = Formalism.UG.cT σ (h.1 * (h⁻¹ * g * h).1) * J * (h.1 * (h⁻¹ * g * h).1) := by
        rw [← hh, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    _ = Formalism.UG.cT σ h.1 * (Formalism.UG.cT σ g.1 * J * g.1) * h.1 := by
        rw [e, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    _ = J' := by rw [hg', hh]

theorem inv_frame (σ : R →+* R) {J J' : Matrix (Fin n) (Fin n) R} {h : GL (Fin n) R}
    (hh : Formalism.UG.cT σ h.1 * J * h.1 = J') : Formalism.UG.cT σ (h⁻¹).1 * J' * (h⁻¹).1 = J := by
  calc _ = Formalism.UG.cT σ (h.1 * (h⁻¹).1) * J * (h.1 * (h⁻¹).1) := by
        rw [← hh, Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    _ = J := by rw [Units.mul_inv, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]

theorem exists_reps {G : Type} [Group G] {K : Subgroup G} {g : G}
    (hK : (K.map (MulAut.conj g).toMonoidHom).relIndex K ≠ 0) :
    ∃ R : Finset G, (∀ γ ∈ R, ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * g * k₂) ∧
      ∀ x : G, (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * g * k₂) → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ K :=
  _root_.UpperTheory.Reformulated.B.Yt3.exists_reps hK

theorem relIndex_conj_ne_zero {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {J U L : Subgroup G}
    (hJ : IsCompact (J : Set G)) (hU : IsOpen (U : Set G)) (hL : ∀ k ∈ L, k ∈ U → k ∈ J) {g : G} (hg : g ∈ L) :
    ((J ⊓ L).map (MulAut.conj g).toMonoidHom).relIndex (J ⊓ L) ≠ 0 := by
  let U' : Subgroup G := U.comap (MulAut.conj g⁻¹).toMonoidHom
  have hU' : IsOpen (U' : Set G) := hU.preimage (show Continuous fun u : G => g⁻¹ * u * g⁻¹⁻¹ by fun_prop)
  have : CompactSpace J := isCompact_iff_compactSpace.1 hJ
  have h1 : U'.relIndex J ≠ 0 := by
    have : Finite (J ⧸ U'.subgroupOf J) :=
      Subgroup.quotient_finite_of_isOpen _ (hU'.preimage continuous_subtype_val)
    exact Subgroup.index_ne_zero_of_finite
  have h2 : U'.relIndex (J ⊓ L) ≠ 0 := fun h => h1 (Subgroup.relIndex_eq_zero_of_le_right inf_le_left h)
  rw [← Subgroup.inf_relIndex_right] at h2
  refine fun h => h2 (Subgroup.relIndex_eq_zero_of_le_left ?_ h)
  rintro k ⟨hk, hk'⟩
  have h3 : g⁻¹ * k * g⁻¹⁻¹ ∈ L := mul_mem (mul_mem (inv_mem hg) hk'.2) (inv_mem (inv_mem hg))
  exact ⟨g⁻¹ * k * g⁻¹⁻¹, ⟨hL _ h3 hk, h3⟩, by simp [mul_assoc]⟩

end Abstract

section Place

open GlobalTheory.PlaceComp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
  (hc : CMData F E) (V : HSpace E) {v : HeightOneSpectrum (𝓞 F)}

theorem divG_iff {e : AF F ⊗[F] E} (he : ∀ w, w ≠ v → evF E w (finP F E e) = 0)
    {h : GL (Fin V.rank) (Fv F v ⊗[F] E)} (hh : IsFrameAt V v h) (ϖ : E) (d : Fin V.rank → ℤ)
    (g : HA (AF F) hc.sig V.gram) :
    DivG hc V e ϖ d g ↔ StdDiv (ordAt E v) (evF E v (finP F E e)) (fun i => inclR (Fv F v) (ϖ ^ d i))
      (h⁻¹ * locMat hc V v g * h).1 := by
  have hback : ∀ y : Fin V.rank → Fv F v ⊗[F] E, h.1 *ᵥ ((h⁻¹).1 *ᵥ y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hback' : ∀ y : Fin V.rank → Fv F v ⊗[F] E, (h⁻¹).1 *ᵥ (h.1 *ᵥ y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  let q : (Fin V.rank → Af F ⊗[F] E) → Fin V.rank → Fv F v ⊗[F] E := fun z i => evF E v (z i)
  let p : (Fin V.rank → Af F ⊗[F] E) → Fin V.rank → Fv F v ⊗[F] E := fun y => (h⁻¹).1 *ᵥ q y
  have p1 : ∀ y, y ∈ lamHat F V → ∀ i, p y i ∈ ordAt E v := fun y hy => (hh _).1 ((mem_lamHat_iff V _).1 hy v)
  have p2 : ∀ y' : Fin V.rank → Fv F v ⊗[F] E, (∀ i, y' i ∈ ordAt E v) → ∃ y, y ∈ lamHat F V ∧ p y = y' :=
    fun y' hy' => ⟨_, GlobalTheory.PlaceDiv.sgT_mem_lamHat V v ((hh (h.1 *ᵥ y')).2 (by rwa [hback'])), by
      simp only [p, q, evF_sgT_self]; exact hback' y'⟩
  have q1 : ∀ z : Fin V.rank → Af F ⊗[F] E, (∀ i, z i ∈ intA F E) → ∀ i, q z i ∈ ordAt E v :=
    fun z hz i => (IntLocal.mem_intA_iff F E _).1 (hz i) v
  have q2 : ∀ z' : Fin V.rank → Fv F v ⊗[F] E, (∀ i, z' i ∈ ordAt E v) →
      ∃ z : Fin V.rank → Af F ⊗[F] E, (∀ i, z i ∈ intA F E) ∧ q z = z' :=
    fun z' hz' => ⟨_, fun i => GlobalTheory.PlaceDiv.sgT_mem_intA v (hz' i), funext fun i => evF_sgT_self v _⟩
  have qv : ∀ (A : Matrix (Fin V.rank) (Fin V.rank) (Af F ⊗[F] E)) z, q (A *ᵥ z) = A.map (evF E v) *ᵥ q z :=
    fun A z => funext fun i => RingHom.map_mulVec (evF E v) A z i
  have qe : ∀ X, q (fun a => finP F E e * X a) = evF E v (finP F E e) • q X :=
    fun X => funext fun i => map_mul (evF E v) _ _
  have key : ∀ X Y : Fin V.rank → Af F ⊗[F] E, ((fun a => finP F E e * X a) = fun a => finP F E e * Y a) ↔
      evF E v (finP F E e) • p X = evF E v (finP F E e) • p Y := by
    intro X Y
    simp only [p, ← Matrix.mulVec_smul, ← qe]
    refine ⟨fun H => by rw [H], fun H => funext fun a => evF_ext fun w => ?_⟩
    by_cases hw : w = v
    · subst hw
      have := congrArg (h.1 *ᵥ ·) H
      simp only [hback] at this
      exact congrFun this a
    · rw [map_mul, map_mul, he w hw, zero_mul, zero_mul]
  have pB : ∀ (B : Matrix (Fin V.rank) (Fin V.rank) (Af F ⊗[F] E)) z,
      p (B *ᵥ z) = ((h⁻¹).1 * B.map (evF E v)) *ᵥ q z := fun B z => by
    simp only [p, qv, Matrix.mulVec_mulVec]
  have pg : ∀ y, p (finMat hc.sig V.gram g *ᵥ y) = (h⁻¹ * locMat hc V v g * h).1 *ᵥ p y := fun y => by
    simp only [p, qv, Units.val_mul, ← Matrix.mulVec_mulVec, hback, locMat_val]
  have qt : ∀ z : Fin V.rank → Af F ⊗[F] E, q (fun i => finP F E (inclR (AF F) (ϖ ^ d i)) * z i) =
      (fun i => inclR (Fv F v) (ϖ ^ d i)) * q z := fun z => funext fun i => by
    show evF E v _ = _ * evF E v _
    rw [map_mul, evF_finP_incl]
  have c1 : ∀ X : Fin V.rank → Af F ⊗[F] E, (fun a => finP F E e * X a) ∈ lamHat F V ↔
      ∀ i, (evF E v (finP F E e) • p X) i ∈ ordAt E v := by
    intro X
    simp only [p, ← Matrix.mulVec_smul, ← qe]
    refine ⟨p1 _, fun H => (mem_lamHat_iff V _).2 fun w => ?_⟩
    by_cases hw : w = v
    · subst hw
      exact (hh _).2 H
    · simp only [map_mul, he w hw, zero_mul]
      exact zero_mem _
  have sB : ∀ B' : Matrix (Fin V.rank) (Fin V.rank) (Fv F v ⊗[F] E),
      ∃ B : Matrix (Fin V.rank) (Fin V.rank) (Af F ⊗[F] E), (h⁻¹).1 * B.map (evF E v) = B' := fun B' => by
    refine ⟨(h.1 * B').map (sgT E v), ?_⟩
    have : ((h.1 * B').map (sgT E v)).map (evF E v) = h.1 * B' := Matrix.ext fun i j => evF_sgT_self v _
    rw [this, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  unfold DivG StdDiv
  rw [Function.Surjective.exists sB]
  refine exists_congr fun B => and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))
  · constructor
    · intro H z' hz'
      obtain ⟨z, hz, rfl⟩ := q2 z' hz'
      rw [← pB, ← c1]
      exact H z hz
    · intro H z hz
      rw [c1, pB]
      exact H _ (q1 z hz)
  · exact forall_exists_transfer p q p1 p2 q1 q2 fun y z => by rw [key, pB]
  · exact forall_exists_transfer p q p1 p2 q1 q2 fun y z => by rw [key, pg, pB, qt]
  · exact forall_exists_transfer q p q1 q2 p1 p2 fun z y => by rw [key, pg, pB, qt]

end Place

section CM

open GlobalTheory.PlaceComp

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
attribute [local instance] IsCMField.starRing

theorem exists_div_iff (hc : CMData (maximalRealSubfield E) E) (V : HSpace E)
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))}
    {e f : AF (maximalRealSubfield E) ⊗[maximalRealSubfield E] E} (hf : IsIdemOf E v f) (hef : e * f = e)
    (ϖ : E) (d : ℕ → ℤ) {n : ℕ} (hn : V.rank = n) :
    (∃ g, Supp hc V f g ∧ DivG hc V e ϖ (fun i => d i.1) g) ↔
      ∃ u ∈ Formalism.UG.UJ (sigR (Fv (maximalRealSubfield E) v) hc.sig) (1 : Matrix (Fin n) (Fin n) _),
        StdDiv (ordAt E v) (evF E v (finP _ E e)) (fun i => inclR (Fv _ v) (ϖ ^ d i.1)) u.1 := by
  subst hn
  obtain ⟨h, hfr, hon⟩ := exists_orthonormal hc V v
  have he : ∀ w, w ≠ v → evF E w (finP _ E e) = 0 := fun w hw => by
    rw [← hef, map_mul, map_mul, hf.2.2 w hw, mul_zero]
  constructor
  · rintro ⟨g, -, hg⟩
    exact ⟨_, conj_mem_UJ _ hon (locMat_mem hc V v g), (divG_iff hc V he hfr ϖ _ g).1 hg⟩
  · rintro ⟨u, hu, hd⟩
    obtain ⟨g, hg, e1⟩ := (GlobalTheory.SuppLocal.supp_local _ E hc V v f hf).2.2 _ (conj_mem_UJ _ (inv_frame _ hon) hu)
    refine ⟨g, hg, (divG_iff hc V he hfr ϖ _ g).2 ?_⟩
    have : h⁻¹ * locMat hc V v g * h = u := by rw [e1]; group
    rwa [this]

end CM

section Host

open Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR Formalism.IndefR.Mult GlobalTheory.IndefiniteRowSideFullHecke.GoodReductionModelReading
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem exists_divAt {V V' : HSp D} (hr : V.rank = V'.rank) {P : HeightOneSpectrum (𝓞 D.host.E)}
    {e f : Formalism.L2.Theta.AE D} (hP : IsPrimeIdem P e f) {ϖ : D.host.E} {d : List ℤ} {α : GA D V} (hα : SuppF V f α)
    (hd : DivAt V e ϖ d α) : ∃ α' : GA D V', SuppF V' f α' ∧ DivAt V' e ϖ d α' := by
  have : IsCMField D.host.E := D.host.isCMField_hostE
  obtain ⟨v, hf, hef⟩ : ∃ v, GlobalTheory.PlaceComp.IsIdemOf D.host.E v f ∧ e * f = e := by
    rcases id hP with ⟨⟨⟨h1, h2, v, ε, ⟨a, rfl, a1, a2⟩, h3⟩, -⟩, rfl⟩ | ⟨rfl, ⟨v, ε, ⟨a, rfl, a1, a2⟩, h3⟩, -⟩
    · exact ⟨v, h3 ▸ GlobalTheory.PlaceComp.isIdemOf_algebraMap a1 a2, by rw [mul_add, h1, h2, add_zero]⟩
    · exact ⟨v, h3 ▸ GlobalTheory.PlaceComp.isIdemOf_algebraMap a1 a2, ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P f f hP).1⟩
  obtain ⟨α', h1, h2⟩ := (exists_div_iff (E := D.host.E) D.sp.cm V' hf hef ϖ (fun i => d.getD i 0) rfl).2
    ((exists_div_iff (E := D.host.E) D.sp.cm V hf hef ϖ (fun i => d.getD i 0) hr).1 ⟨α, hα, hd.2⟩)
  exact ⟨α', h1, hd.1.trans hr, h2⟩

theorem exists_isCosetRep (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)
    {P : HeightOneSpectrum (𝓞 D.host.E)} {e f : Formalism.L2.Theta.AE D} (hP : IsPrimeIdem P e f) {α : GA D V}
    (hα : SuppF V f α) : ∃ R : Finset (GA D V), (∀ γ ∈ R, SuppF V f γ) ∧
      IsCosetRep V {k | k ∈ (Lev.levG V β L : Set (GA D V)) ∧ SuppF V f k} α R := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  obtain ⟨h1, h2, hG, -⟩ := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e f hP
  obtain ⟨S, hS⟩ := ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).1 f h1 h2).1
  obtain ⟨R, r1, r2⟩ := exists_reps (relIndex_conj_ne_zero (L := S) (GlobalTheory.ParahoricCompact.isCompact_levG V β L)
    (GlobalTheory.ParahoricCompact.isOpen_comap_lev V β L) (fun k hk hk' => ⟨hG k ((hS k).1 hk), hk'⟩) ((hS α).2 hα))
  have hK : {k | k ∈ (Lev.levG V β L : Set (GA D V)) ∧ SuppF V f k} = (Lev.levG V β L ⊓ S : Subgroup (GA D V)) :=
    Set.ext fun k => and_congr_right fun _ => (hS k).symm
  have r0 : ∀ γ ∈ R, SuppF V f γ := fun γ hγ => by
    obtain ⟨a, ha, b, hb, rfl⟩ := r1 γ hγ
    exact (hS _).1 (mul_mem (mul_mem ha.2 ((hS α).2 hα)) hb.2)
  rw [hK]
  exact ⟨R, r0, fun γ hγ => ⟨hG γ (r0 γ hγ), r1 γ hγ⟩, r2⟩

end Host

end GlobalTheory.HeckeLabels
