import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Formalism.LocalToGlobal.IndefiniteReal.IsMultMapUnivZero
import Formalism.LocalToGlobal.IndefiniteReal.PartsRow
import Development.AbelianVarietyTheory.Definitions.Divisors.InstCMHostS
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodFixedVectorOfTypeOccurringInRows
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankWEigenpartEqRowsFullHecke
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicIsometryMatchingFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBaseLevelVectorOfPrincipalLevelFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarRowsLevelCharacterEqLiftsLevelCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateModelsMultiplicityEqual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCompatFiniteIsometry
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplexConjugationMapsMultiplicitySpaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.CuspMult

noncomputable section
namespace GlobalTheory.KapIsot

section Similitude

variable {R : Type} [CommRing R] {σ : R →+* R} {n : ℕ}

open ReciprocityTheory.Aut in

theorem scalar_of_comm (hσ : ∀ x, σ (σ x) = x) (h2 : IsUnit (2 : R)) (a : Matrix (Fin n) (Fin n) R)
    (ha : ∀ κ ∈ UGroup n σ hσ, a * κ.val = κ.val * a) (i₀ : Fin n) : a = a i₀ i₀ • (1 : Matrix (Fin n) (Fin n) R) := by
  have key : ∀ P : Matrix (Fin n) (Fin n) R, P * P = 1 → conjT σ P = P → a * P = P * a := fun P h1 h3 =>
    ha ⟨P, P, h1, h1⟩ (by show P * conjT σ P = 1; rw [h3, h1])
  ext i j
  by_cases hij : i = j
  · subst hij
    have := key (Matrix.swap R i₀ i) (Matrix.swap_mul_self _ _) (by rw [conjT, Matrix.map_swap, Matrix.transpose_swap])
    have e := congrFun (congrFun this i₀) i
    rw [Matrix.mul_swap_apply_right, Matrix.swap_mul_apply_left] at e
    simp [e]
  · have := key (Matrix.diagonal (Function.update 1 i (-1))) (by
      rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext k
      by_cases hk : k = i
      · subst hk; simp
      · simp [Function.update_of_ne hk]) (by
      rw [conjT, Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose]
      congr 1
      funext k
      by_cases hk : k = i
      · subst hk; simp
      · simp [Function.update_of_ne hk])
    have e := congrFun (congrFun this i) j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Function.update_self, Function.update_of_ne (Ne.symm hij)] at e
    have e2 : 2 * a i j = 0 := by
      simp only [Pi.one_apply] at e
      linear_combination e
    rw [(h2.mul_right_eq_zero).1 e2]
    simp [hij]

open ReciprocityTheory.Aut in

theorem exists_unitary_conj : ∀ {R : Type} [CommRing R] (σ : R →+* R) (hσ : ∀ x, σ (σ x) = x) {n : ℕ}, IsUnit (2 : R) → Odd n → ∀ g : GL (Fin n) R, (∀ κ ∈ ReciprocityTheory.Aut.UGroup n σ hσ, g * κ * g⁻¹ ∈ ReciprocityTheory.Aut.UGroup n σ hσ) → ∃ h ∈ ReciprocityTheory.Aut.UGroup n σ hσ, ∀ κ : GL (Fin n) R, g * κ * g⁻¹ = h * κ * h⁻¹ := by
  intro R _ σ hσ n h2 hn g hg
  obtain ⟨k, rfl⟩ := hn
  set a : Matrix (Fin (2 * k + 1)) (Fin (2 * k + 1)) R := conjT σ g.val * g.val with hadef
  have hcomm : ∀ κ ∈ UGroup (2 * k + 1) σ hσ, a * κ.val = κ.val * a := by
    intro κ hκ
    have h1 : κ.val * conjT σ κ.val = 1 := hκ
    have h3 : conjT σ (g * κ * g⁻¹).val * (g * κ * g⁻¹).val = 1 := mul_eq_one_comm.1 (hg κ hκ)
    have h4 : g.val * κ.val = (g * κ * g⁻¹).val * g.val := by rw [← Units.val_mul, ← Units.val_mul, inv_mul_cancel_right]
    have h5 : conjT σ (g.val * κ.val) * (g.val * κ.val) = a := by
      rw [h4, conjT_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (conjT σ (g * κ * g⁻¹).val), h3, Matrix.one_mul]
    calc a * κ.val = κ.val * conjT σ κ.val * a * κ.val := by rw [h1, Matrix.one_mul]
      _ = κ.val * (conjT σ (g.val * κ.val) * (g.val * κ.val)) := by rw [conjT_mul, hadef]; simp only [Matrix.mul_assoc]
      _ = κ.val * a := by rw [h5]
  obtain ⟨t, ht⟩ : ∃ t : R, a = t • (1 : Matrix (Fin (2 * k + 1)) (Fin (2 * k + 1)) R) := ⟨_, scalar_of_comm hσ h2 a hcomm 0⟩
  have hσt : σ t = t := by
    have h1 : conjT σ a = a := by rw [hadef, conjT_mul, conjT_conjT σ hσ]
    rw [ht] at h1
    simpa [conjT] using congrFun (congrFun h1 0) 0
  have hdet : σ g.val.det * g.val.det = t ^ (2 * k + 1) := by
    have h1 := congrArg Matrix.det ht
    rw [hadef, Matrix.det_mul, conjT, Matrix.det_transpose, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at h1
    rw [← h1, RingHom.map_det]
    rfl
  obtain ⟨d, hd⟩ : IsUnit g.val.det := (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
  have hd' : σ (d⁻¹ : Rˣ) * σ d = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  have htu : IsUnit t := by
    rw [← isUnit_pow_iff (Nat.succ_ne_zero (2 * k)), ← hdet, ← hd]
    exact (d.isUnit.map σ).mul d.isUnit
  obtain ⟨u, rfl⟩ := htu
  let z : Rˣ := d⁻¹ * u ^ k
  have hz : σ z * z * u = 1 := by
    rw [← hd] at hdet
    simp only [z, Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, hσt]
    have e1 : ((d⁻¹ : Rˣ) : R) * d = 1 := d.inv_mul
    calc _ = σ (d⁻¹ : Rˣ) * (d⁻¹ : Rˣ) * (u : R) ^ (2 * k + 1) := by ring
      _ = (σ (d⁻¹ : Rˣ) * σ d) * (((d⁻¹ : Rˣ) : R) * d) := by rw [← hdet]; ring
      _ = 1 := by rw [hd', e1, one_mul]
  refine ⟨⟨(z : R) • g.val, ((z⁻¹ : Rˣ) : R) • (g⁻¹).val, ?_, ?_⟩, ?_, fun κ => Units.ext ?_⟩
  · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Units.mul_inv, Units.mul_inv, one_smul]
  · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Units.inv_mul, Units.inv_mul, one_smul]
  · show ((z : R) • g.val) * conjT σ ((z : R) • g.val) = 1
    rw [mul_eq_one_comm]
    have : conjT σ ((z : R) • g.val) = σ z • conjT σ g.val := by
      ext i j; simp [conjT]
    rw [this, Matrix.smul_mul, Matrix.mul_smul, ← hadef, ht, smul_smul, smul_smul, hz, one_smul]
  · show _ = ((z : R) • g.val) * κ.val * (((z⁻¹ : Rˣ) : R) • (g⁻¹).val)
    rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, Units.mul_inv, one_smul]
    rfl

end Similitude

theorem block_frame_conjugation_identity {R : Type} [CommRing R] {a b c : ℕ} (bW : Matrix (Fin a) (Fin b) R) (bW' : Matrix (Fin b) (Fin a) R)
    (bY : Matrix (Fin c) (Fin b) R) (bY' : Matrix (Fin b) (Fin c) R) (J : Matrix (Fin a) (Fin c) R) (J' : Matrix (Fin c) (Fin a) R)
    (K K' : Matrix (Fin b) (Fin b) R) (hW : bW' * bW = 1) (hJ : J * J' = 1) (hc : bW * K' * bW' * J = J * (bY * K * bY')) :
    bW' * J * bY * K * (bY' * J' * bW) = K' := by
  calc _ = bW' * (J * (bY * K * bY')) * J' * bW := by simp only [Matrix.mul_assoc]
    _ = (bW' * bW) * K' * (bW' * (J * J') * bW) := by rw [← hc]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [hJ, Matrix.mul_one, hW, Matrix.one_mul, Matrix.mul_one]

set_option maxHeartbeats 1000000 in

theorem frames_inner : ∀ {D : D7} (Y W : HSp D) {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (PY : principalLevelFrame.RowPsi Y n) (PW : principalLevelFrame.RowPsi W n), GlobalTheory.StdFrame.StdPsi hF PY → GlobalTheory.StdFrame.StdPsi hF PW → Odd Y.rank → ∀ (β : GL (Fin Y.rank) (Lev.EAf D)) (β' : GL (Fin W.rank) (Lev.EAf D)) (Pg : Finset (Pl D.host.E)) (j : Matrix (Fin W.rank) (Fin Y.rank) (Lev.EAf D)) (Φ : GfC Y ≃ₜ* GfC W), GlobalTheory.CuspMult.IsFinIso Y W β β' Pg j Φ → ∃ h : Formalism.AUTREP.GAf D.host.E n, ∀ κ, ((Φ ⟨PY.ψ κ, PY.into κ⟩ : GfC W) : GA D W) = PW.ψ (h * κ * h⁻¹) := by
  intro D Y W n hF PY PW hY hW hodd β β' Pg j Φ hI
  obtain ⟨⟨bY, bY', hY1, hY2, hYf⟩, -⟩ := hY
  obtain ⟨⟨bW, bW', hW1, hW2, hWf⟩, -⟩ := hW
  choose k hk using fun κ => PW.onto _ (Φ ⟨PY.ψ κ, PY.into κ⟩).2
  suffices H : ∃ h : Formalism.AUTREP.GAf D.host.E n, ∀ κ, k κ = h * κ * h⁻¹ by
    obtain ⟨h, hh⟩ := H
    exact ⟨h, fun κ => by rw [← hk, hh]⟩
  let t := GlobalTheory.StdFrame.tensCastR hF
  rcases subsingleton_or_nontrivial (ReciprocityTheory.Aut.AL D.host.E) with hs | hs
  · exact ⟨1, fun κ => Subtype.ext (Units.ext (Subsingleton.elim _ _))⟩
  haveI := t.toEquiv.nontrivial
  have hn : Odd n := by
    have := Matrix.square_of_invertible bY bY' hY1 hY2
    rw [Fintype.card_fin, Fintype.card_fin] at this
    rwa [← this]
  obtain ⟨hr, u, hu, -⟩ := hI.frame
  obtain ⟨⟨j', h1, h2⟩, -⟩ := GlobalTheory.HeckeTrans.frame_inv (Formalism.L2.Herm.intAf D.host.F D.host.E) β β' (finCongr hr)
    (intGL D.host.F D.host.E W.rank u) u.val (u⁻¹).val rfl rfl j hu
  have h1' := GlobalTheory.HeckeTrans.map_mul_one (GlobalTheory.HeckeTrans.unswap D) h1
  have h2' := GlobalTheory.HeckeTrans.map_mul_one (GlobalTheory.HeckeTrans.unswap D) h2
  set J := j.map (GlobalTheory.HeckeTrans.unswap D)
  set J' := j'.map (GlobalTheory.HeckeTrans.unswap D)
  have hX : bW' * J * bY * (bY' * J' * bW) = 1 := by
    calc _ = bW' * (J * (bY * bY') * J') * bW := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hY1, Matrix.mul_one, h1', Matrix.mul_one, hW2]
  have hX' : (bW' * J * bY).map t * (bY' * J' * bW).map t = 1 := by
    rw [← Matrix.map_mul, hX, Matrix.map_one _ (map_zero t) (map_one t)]
  let g : GL (Fin n) (ReciprocityTheory.Aut.AL D.host.E) := ⟨(bW' * J * bY).map t, (bY' * J' * bW).map t, hX', mul_eq_one_comm.1 hX'⟩
  have hg : ∀ κ : Formalism.AUTREP.GAf D.host.E n, g * κ.1 * g⁻¹ = (k κ).1 := by
    intro κ
    have hc := congrArg (fun M => Matrix.map M (GlobalTheory.HeckeTrans.unswap D)) (hI.conj ⟨PY.ψ κ, PY.into κ⟩)
    simp only [Matrix.map_mul, GlobalTheory.HeckeTrans.finE_unswap] at hc
    rw [← hk κ, hWf, hYf] at hc
    have e := block_frame_conjugation_identity bW bW' bY bY' J J' _ _ hW2 h1' hc
    have e' := congrArg (fun M => Matrix.map M t) e
    simp only [Matrix.map_mul] at e'
    apply Units.ext
    have m : ∀ M : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E), (M.map t.symm).map t = M := fun M => by
      ext a b
      exact t.apply_symm_apply _
    rw [m, m] at e'
    rw [← e']
    show (bW' * J * bY).map t * κ.1.val * (bY' * J' * bW).map t = _
    simp only [Matrix.map_mul]
  have h2u : IsUnit (2 : ReciprocityTheory.Aut.AL D.host.E) := by
    have := (two_ne_zero (α := D.host.E)).isUnit.map (algebraMap D.host.E (ReciprocityTheory.Aut.AL D.host.E))
    rwa [map_ofNat] at this
  obtain ⟨h, hU, hh⟩ := exists_unitary_conj _ (ReciprocityTheory.Aut.conjAL_conjAL D.host.E) h2u hn g fun κ hκ => by
    rw [hg ⟨κ, hκ⟩]
    exact (k ⟨κ, hκ⟩).2
  exact ⟨⟨h, hU⟩, fun κ => Subtype.ext ((hg κ).symm.trans (hh κ.1))⟩

set_option maxHeartbeats 1000000 in

theorem exists_conj_map : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {n : ℕ} (PY : principalLevelFrame.RowPsi (Yc D 0) n) π, π ∈ principalLevelFrame.OccRows R.θ PY (R.MY 0) (fun b => (levS _ (R.βY 0) (R.dat0 (R.levR F b)))) (fun b => (levChi _ (R.βY 0) (R.dat0 (R.levR F b)))) (fun _ => R.e0) → ∃ (M₀ : DSModel (Yc D 0) (parA (Ptw D) 0)) (f : π.S →ₗ[ℂ] MMap M₀), f ≠ 0 ∧ principalLevelFrame.IsEqvA (principalLevelFrame.actM PY M₀) π f ∧ ∀ x, f x ∈ GlobalTheory.CuspMult.allMaps R.θ M₀ := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F n PY π hπ
  obtain ⟨b, hb⟩ := hπ
  obtain ⟨Φ, hΦ, hΦ0⟩ : ∃ Φ : (principalLevelFrame.FinTyp.conjT π).S →ₗ[ℂ] MMap (R.MY 0),
      (principalLevelFrame.IsEqvA (principalLevelFrame.actM PY (R.MY 0)) (principalLevelFrame.FinTyp.conjT π) Φ ∧ LinearMap.range Φ ≤ principalLevelFrame.Minf R.θ PY (R.MY 0)) ∧ Φ ≠ 0 := by
    by_contra hno
    apply hb
    refine eq_bot_iff.2 (inf_le_right.trans (iSup₂_le fun Φ hΦ => ?_))
    have : Φ = 0 := by
      by_contra h0
      exact hno ⟨Φ, hΦ, h0⟩
    rw [this, LinearMap.range_zero]
  obtain ⟨M₀, c, hc⟩ := GlobalTheory.PartDims.exists_conjModel (S' := parA (Ptw D) 0)
    (fun τ => by rw [Nat.zero_min]; exact (dualPar_dualPar _).symm) (R.MY 0)
  obtain ⟨h, hM⟩ := GlobalTheory.T.complexConjugation_maps_multiplicitySpace R.θ (R.MY 0) M₀ c hc
  let st : π.S → (principalLevelFrame.FinTyp.conjT π).S := fun x => ⟨fun g => star (x.1 g), by
    show (fun g => star (star (x.1 g))) ∈ π.S
    simp only [star_star]
    exact x.2⟩
  have hadd : ∀ x y, st (x + y) = st x + st y := fun x y => Subtype.ext (funext fun g => star_add _ _)
  have hsmul : ∀ (a : ℂ) x, st (a • x) = star a • st x := fun a x => Subtype.ext (funext fun g => star_mul' a (x.1 g))
  let f : π.S →ₗ[ℂ] MMap M₀ :=
    { toFun := fun x => GlobalTheory.ConjDim.conjMap (R.MY 0) M₀ c h (Φ (st x))
      map_add' := fun x y => by
        rw [hadd, map_add]
        exact MultilinearMap.ext fun v' => star_add _ _
      map_smul' := fun a x => by
        rw [hsmul, map_smul]
        refine MultilinearMap.ext fun v' => ?_
        show star (star a • Φ (st x) _) = a • star (Φ (st x) _)
        rw [star_smul, star_star] }
  refine ⟨M₀, f, fun h0 => hΦ0 (LinearMap.ext fun x => ?_), fun κ x => ?_, fun x => ?_⟩
  · have e : st ⟨fun g => star (x.1 g), x.2⟩ = x := Subtype.ext (funext fun g => star_star _)
    have := GlobalTheory.ConjDim.conjMap_eq_zero (R.MY 0) M₀ c h _ (LinearMap.congr_fun h0 ⟨fun g => star (x.1 g), x.2⟩)
    rwa [e] at this
  · have e := hΦ.1 κ (st x)
    show GlobalTheory.ConjDim.conjMap (R.MY 0) M₀ c h (Φ ⟨Formalism.L2.NG.rt D.host.E n κ (st x), _⟩) = _
    rw [e]
    rfl
  · have h1 : Φ (st x) ∈ allMaps R.θ (R.MY 0) :=
      (iSup_le fun N => GlobalTheory.PartDims.mult_le R.θ _ fun k hk => hk.elim : principalLevelFrame.Minf R.θ PY (R.MY 0) ≤ allMaps R.θ (R.MY 0))
        (hΦ.2 ⟨_, rfl⟩)
    obtain ⟨T', hT', e1⟩ := hM ∅ (fun _ => 1) _ h1
    have : f x = T' := by
      refine MultilinearMap.ext fun v' => funext fun g => ?_
      rw [e1 v' (fun τ => ⟨c τ (v' τ), (h τ _).1 (v' τ).2⟩) (fun _ => rfl) g]
      rfl
    rw [this]
    exact GlobalTheory.PartDims.mult_le R.θ _ (fun k hk => hk.elim) hT'

open Formalism.IndefR.principalLevelFrame in

theorem exists_good_base_vec : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, A.fam.Ok s → GlobalTheory.Hk3.Core R F → (∀ χ ∈ A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → ∀ {n : ℕ} (PY : principalLevelFrame.RowPsi (Yc D 0) n) (π : Formalism.L2.NG.FinTyp D.host.E n) (v : Formalism.AUTREP.GAf D.host.E n → ℂ), v ∈ π.S → v ≠ 0 → principalLevelFrame.IsTypeVec (PY.ψ ⁻¹' levS _ (R.βY 0) (R.dat0 R.triv)) (fun _ => 1) v → (∀ κ : G → Formalism.AUTREP.GAf D.host.E n, (∀ g, IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g) (PY.ψ (κ g))) → ∑ g, RealDat.eC (A := A) D.what₂.embLL g • Formalism.L2.NG.rt D.host.E n (κ g) v = v) → ∃ x ∈ π.S, x ≠ 0 ∧ principalLevelFrame.IsTypeVec (PY.ψ ⁻¹' levS _ (R.βY 0) (R.dat0 (R.levR F false))) (fun κ => levChi _ (R.βY 0) (R.dat0 (R.levR F false)) (PY.ψ κ)) x ∧ ∀ κ : G → Formalism.AUTREP.GAf D.host.E n, (∀ g, IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g) (PY.ψ (κ g))) → ∑ g, RealDat.eC (A := A) D.what₂.embLL g • Formalism.L2.NG.rt D.host.E n (κ g) x = x := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F s hOk hC hne n PY π v hvS hv0 hvT hgood
  classical
  have hL := GlobalTheory.DimFull.liftsY' hC
  have hex : ∀ g : G, ∃ κ : Formalism.AUTREP.GAf D.host.E n,
      IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g) (PY.ψ κ) := by
    intro g
    obtain ⟨κ, hκ⟩ := hL (R.eG g)
    obtain ⟨h, rfl⟩ := PY.onto κ hκ.1
    exact ⟨h, hκ⟩
  choose k hk using hex
  set J0 := PY.ψ ⁻¹' levS _ (R.βY 0) (R.dat0 R.triv) with hJ0
  have hvfix : ∀ c ∈ J0, Formalism.L2.NG.rt D.host.E n c v = v := fun c hc => by
    simpa using hvT c hc
  set Ws : Submodule ℂ (Formalism.AUTREP.GAf D.host.E n → ℂ) :=
    Submodule.span ℂ (Set.range fun g => Formalism.L2.NG.rt D.host.E n (k g) v) with hWs
  have hfix : ∀ w ∈ Ws, ∀ c ∈ J0, Formalism.L2.NG.rt D.host.E n c w = w := by
    intro w hw c hc
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      have hc' : (k g)⁻¹ * c * k g ∈ J0 := by
        rw [hJ0, Set.mem_preimage]
        rw [map_mul, map_mul, map_inv]
        exact GlobalTheory.BaseVec.conj_mem_principal R hc (hk g).1 (hk g).2.1
      rw [rt_rt, show c * k g = k g * ((k g)⁻¹ * c * k g) by group, ← rt_rt, hvfix _ hc']
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | smul a x _ hx => rw [map_smul, hx]
  have hprod : ∀ g h, ∀ w ∈ Ws, Formalism.L2.NG.rt D.host.E n (k g) (Formalism.L2.NG.rt D.host.E n (k h) w) =
      Formalism.L2.NG.rt D.host.E n (k (g * h)) w := by
    intro g h w hw
    have hl : IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG (g * h)) (PY.ψ (k g * k h)) := by
      refine ⟨?_, ?_, ?_⟩
      · rw [map_mul]; exact (GfC _).mul_mem (hk g).1 (hk h).1
      · rw [map_mul, map_mul]; exact Subgroup.mul_mem _ (hk g).2.1 (hk h).2.1
      · rw [map_mul, map_mul, rTup_mul (hk g).2.1 (hk h).2.1, (hk g).2.2, (hk h).2.2]
        exact (map_mul R.eG g h).symm
    have hc : (k (g * h))⁻¹ * (k g * k h) ∈ J0 := by
      rw [hJ0, Set.mem_preimage]
      rw [map_mul, map_inv]
      exact GlobalTheory.BaseVec.lift_div_principal R (hk (g * h)) hl
    rw [rt_rt, show k g * k h = k (g * h) * ((k (g * h))⁻¹ * (k g * k h)) by group, ← rt_rt, hfix w hw _ hc]
  have hk1 : k 1 ∈ J0 := by
    rw [hJ0, Set.mem_preimage, GlobalTheory.BaseVec.mem_levS]
    refine ⟨(hk 1).1, (hk 1).2.1, Subgroup.mem_bot.2 ?_⟩
    rw [(hk 1).2.2]
    exact map_one R.eG
  have hvWs : v ∈ Ws := by
    have : Formalism.L2.NG.rt D.host.E n (k 1) v ∈ Ws := Submodule.subset_span ⟨1, rfl⟩
    rwa [hvfix _ hk1] at this
  have hstab : ∀ g, ∀ w ∈ Ws, Formalism.L2.NG.rt D.host.E n (k g) w ∈ Ws := by
    intro g w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      rw [hprod g h v hvWs]
      exact Submodule.subset_span ⟨g * h, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Ws.add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact Ws.smul_mem a hx
  let ρ : Representation ℂ G Ws :=
    { toFun := fun g => (Formalism.L2.NG.rt D.host.E n (k g)).restrict (fun w hw => hstab g w hw)
      map_one' := LinearMap.ext fun w => Subtype.ext (hfix w w.2 _ hk1)
      map_mul' := fun g h => LinearMap.ext fun w => Subtype.ext (hprod g h w w.2).symm }
  haveI : FiniteDimensional ℂ Ws := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have hX : ∀ χ ∈ A.X, IsAbsIrrChar χ := hOk.irr
  have hcen : ∀ g h : G, RealDat.eC (A := A) D.what₂.embLL (g * h * g⁻¹) = RealDat.eC (A := A) D.what₂.embLL h := fun g h => by
    unfold RealDat.eC
    rw [GlobalTheory.BaseVec.coeff_conj_of_central _ (fun b => idemOf_central A.X hX b) g h]
  have hgoodv : ∑ g, RealDat.eC (A := A) D.what₂.embLL g • Formalism.L2.NG.rt D.host.E n (k g) v = v := hgood k hk
  have hgoodW : ∀ w ∈ Ws, ∑ g, RealDat.eC (A := A) D.what₂.embLL g • Formalism.L2.NG.rt D.host.E n (k g) w = w := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      simp only [hprod _ h v hvWs]
      conv_rhs => rw [← hgoodv]
      rw [map_sum]
      simp only [map_smul, hprod h _ v hvWs]
      refine Fintype.sum_equiv (MulAut.conj h⁻¹).toEquiv _ _ fun g => ?_
      simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
      rw [hcen, show h * (h⁻¹ * g * h⁻¹⁻¹) = g * h by group]
    | zero => simp
    | add x y _ _ hx hy => simp only [map_add, smul_add, Finset.sum_add_distrib, hx, hy]
    | smul a x _ hx =>
      simp only [map_smul]
      simp only [smul_comm _ a, ← Finset.smul_sum, hx]
  have hbot : (⊤ : Submodule ℂ Ws) ≠ ⊥ := by
    intro h
    have h0 : (⟨v, hvWs⟩ : Ws) ∈ (⊥ : Submodule ℂ Ws) := h ▸ Submodule.mem_top
    exact hv0 (congrArg Subtype.val ((Submodule.mem_bot ℂ).1 h0))
  obtain ⟨u, -, hu0, hu⟩ := GlobalTheory.Hk3.exists_level_vector D.what₂.embLL A.X F.P0 F.ψ0 ρ ⊤ hX hne (fun _ => le_top) hbot
    (fun u _ => Subtype.ext (by
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      exact hgoodW u u.2))
  refine ⟨(u : Formalism.AUTREP.GAf D.host.E n → ℂ), ?_, fun h => hu0 (Subtype.ext h), ?_, ?_⟩
  · exact (Submodule.span_le.2 (by rintro _ ⟨g, rfl⟩; exact π.stable _ _ hvS)) u.2
  · intro κ hκ
    obtain ⟨h1, h2, h3⟩ := (GlobalTheory.BaseVec.mem_levS R _ (PY.ψ κ)).1 hκ
    have hgP : R.eG.symm (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (PY.ψ κ))) ∈ F.P0 := h3
    have hl : IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv)
        (R.eG (R.eG.symm (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (PY.ψ κ))))) (PY.ψ κ) :=
      ⟨h1, h2, (MulEquiv.apply_symm_apply R.eG _).symm⟩
    have hc : (k (R.eG.symm (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (PY.ψ κ)))))⁻¹ * κ ∈ J0 := by
      rw [hJ0, Set.mem_preimage]
      rw [map_mul, map_inv]
      exact GlobalTheory.BaseVec.lift_div_principal R (hk _) hl
    have e1 : Formalism.L2.NG.rt D.host.E n κ (u : _ → ℂ) =
        Formalism.L2.NG.rt D.host.E n (k (R.eG.symm (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (PY.ψ κ))))) u := by
      conv_lhs => rw [show κ = k (R.eG.symm (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (PY.ψ κ)))) *
        ((k (R.eG.symm (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (PY.ψ κ)))))⁻¹ * κ) by group]
      rw [← rt_rt, hfix u u.2 _ hc]
    have e2 := congrArg Subtype.val (hu ⟨_, hgP⟩)
    rw [e1]
    refine e2.trans ?_
    show _ = levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F false)) (PY.ψ κ) • _
    rw [GlobalTheory.BaseVec.principalRowLevelCharacter_trivial, Submodule.coe_smul]
    congr 1
    exact ((congrArg (fun u : ℂˣ => (u : ℂ)) (extendOne_of_mem (R.levR F false).chi h3)).trans rfl).symm
  · intro κ hκ
    refine Eq.trans (Finset.sum_congr rfl fun g _ => ?_) (hgoodW u u.2)
    have hc : (k g)⁻¹ * κ g ∈ J0 := by
      rw [hJ0, Set.mem_preimage, map_mul, map_inv]
      exact GlobalTheory.BaseVec.lift_div_principal R (hk g) (hκ g)
    rw [show κ g = k g * ((k g)⁻¹ * κ g) by group, ← rt_rt, hfix u u.2 _ hc]

theorem exists_good_vec : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ}, A.fam.Ok s → GlobalTheory.Hk3.Core R F → Formalism.L2.DIV.GoodStable A.X → (∀ χ ∈ A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → ∀ {n : ℕ} (PY : principalLevelFrame.RowPsi (Yc D 0) n) π, π ∈ principalLevelFrame.OccRows R.θ PY (R.MY 0) (fun b => (levS _ (R.βY 0) (R.dat0 (R.levR F b)))) (fun b => (levChi _ (R.βY 0) (R.dat0 (R.levR F b)))) (fun _ => R.e0) → ∃ y ∈ π.S, y ≠ 0 ∧ principalLevelFrame.IsTypeVec (PY.ψ ⁻¹' levS _ (R.βY 0) (R.dat0 (R.levL F false (sg0 D A)))) (fun κ => levChi _ (R.βY 0) (R.dat0 (R.levL F false (sg0 D A))) (PY.ψ κ)) y ∧ ∀ κ : G → Formalism.AUTREP.GAf D.host.E n, (∀ g, IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) (R.eG g) (PY.ψ (κ g))) → ∑ g, RealDat.eC (A := A) D.what₂.embLL g • Formalism.L2.NG.rt D.host.E n (κ g) y = y := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F s hOk hC hX hgen n PY π hπ
  obtain ⟨v, hvS, hv0, hvT, hvG⟩ := GlobalTheory.OccRowVec.exists_vec_of_occRows R F hOk hC PY π hπ
  obtain ⟨x, hxS, hx0, hxT, hxG⟩ := exists_good_base_vec R F hOk hC hgen PY (principalLevelFrame.FinTyp.conjT π) v hvS hv0 hvT hvG
  refine ⟨fun g => star (x g), hxS, fun h => hx0 (funext fun g => star_eq_zero.1 (congrFun h g)), fun κ hκ => ?_, fun κ hκ => ?_⟩
  · funext g
    have eg := congrFun (hxT κ hκ) g
    simp only [principalLevelFrame.rt_apply, Pi.smul_apply, smul_eq_mul] at eg
    simp only [principalLevelFrame.rt_apply, Pi.smul_apply, smul_eq_mul, eg, star_mul', GlobalTheory.ChiStarLev.star_levChi_levR R F false]
  · funext g
    have eg := congrArg star (congrFun (hxG κ hκ) g)
    rw [← eg, Finset.sum_apply, Finset.sum_apply, star_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have := GlobalTheory.T.star_idemOf_coeff_eq_self D.what₂.embLL A.X hOk.irr hX a
    simp only [principalLevelFrame.rt_apply, Pi.smul_apply, smul_eq_mul, star_mul']
    congr 1
    exact this.symm

section Abstract

variable {H S X : Type} [Group H] [AddCommGroup S] [Module ℂ S] [AddCommGroup X] [Module ℂ X]
  {σ : Representation ℂ H S} {ρ : Representation ℂ H X}

theorem injective_of (hirr : ∀ U : Submodule ℂ S, (∀ g, ∀ x ∈ U, σ g x ∈ U) → U = ⊥ ∨ U = ⊤) {f : S →ₗ[ℂ] X}
    (hf : ∀ g s, f (σ g s) = ρ g (f s)) (h0 : f ≠ 0) : Function.Injective f := by
  rcases hirr (LinearMap.ker f) (fun g x hx => by rw [LinearMap.mem_ker, hf, LinearMap.mem_ker.1 hx, map_zero]) with h | h
  · exact LinearMap.ker_eq_bot.1 h
  · exact absurd (LinearMap.ker_eq_top.1 h) h0

theorem isIrreducible_of [Nontrivial S] (hirr : ∀ U : Submodule ℂ S, (∀ g, ∀ x ∈ U, σ g x ∈ U) → U = ⊥ ∨ U = ⊤) :
    σ.IsIrreducible := by
  haveI : Nontrivial (Subrepresentation σ) := ⟨⟨⊥, ⊤, fun h => by
    have := congrArg Subrepresentation.toSubmodule h
    exact bot_ne_top (α := Submodule ℂ S) this⟩⟩
  refine ⟨fun U => ?_⟩
  rcases hirr U.toSubmodule (fun g x hx => U.apply_mem_toSubmodule g hx) with h | h
  · exact Or.inl (Subrepresentation.toSubmodule_injective h)
  · exact Or.inr (Subrepresentation.toSubmodule_injective h)

theorem killed_map {f : S →ₗ[ℂ] X} (hf : ∀ g s, f (σ g s) = ρ g (f s)) {I : Set (MonoidAlgebra ℂ H)} {s : S}
    (hs : s ∈ killed σ I) : f s ∈ killed ρ I := by
  rw [mem_killed] at hs ⊢
  intro x hx
  have key : ∀ x : MonoidAlgebra ℂ H, ρ.asAlgebraHom x (f s) = f (σ.asAlgebraHom x s) := by
    intro x
    induction x using MonoidAlgebra.induction_on with
    | of g => simp [hf]
    | add a b ha hb => simp [ha, hb]
    | smul a b hb => simp [hb]
  rw [key, hs x hx, map_zero]

theorem isAdmissible_of [TopologicalSpace H] [IsTopologicalGroup H]
    (hirr : ∀ U : Submodule ℂ S, (∀ g, ∀ x ∈ U, σ g x ∈ U) → U = ⊥ ∨ U = ⊤) {y : S} (hy : y ≠ 0)
    (ho : IsOpen {g : H | σ g y = y}) {C : Submodule ℂ X} {f : S →ₗ[ℂ] X} (hf : f ∈ homInto σ ρ C) (h0 : f ≠ 0)
    (hfin : ∀ K : Subgroup H, IsOpen (K : Set H) → FiniteDimensional ℂ ↥(C ⊓ GlobalTheory.PRep.fixed ρ K)) :
    GlobalTheory.PRep.IsAdmissible σ := by
  refine ⟨fun v => ?_, fun K hK _ => ?_⟩
  · rcases hirr (GlobalTheory.PRep.smoothPart σ) (GlobalTheory.PRep.smoothPart_stable σ) with h | h
    · exact absurd ((Submodule.eq_bot_iff _).1 h y ho) hy
    · exact (h.ge Submodule.mem_top : v ∈ GlobalTheory.PRep.smoothPart σ)
  · haveI := hfin K hK
    refine FiniteDimensional.of_injective (f.restrict (p := GlobalTheory.PRep.fixed σ K) (q := C ⊓ GlobalTheory.PRep.fixed ρ K)
      fun v hv => ⟨hf.1 v, GlobalTheory.CuspDec.mem_fixed.2 fun k hk => ?_⟩) fun a b h => ?_
    · rw [← hf.2, GlobalTheory.CuspDec.mem_fixed.1 hv k hk]
    · exact Subtype.ext (injective_of hirr hf.2 h0 (congrArg Subtype.val h))

end Abstract

theorem odd_r (R : Ranks) : Odd R.r := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨b, hb⟩ := R.m_even
  have h2 := R.two_le_m
  exact ⟨a + b - 1, by simp only [Ranks.r]; omega⟩

def eqv {D : D7} {Y : HSp D} {n : ℕ} (P : principalLevelFrame.RowPsi Y n) : Formalism.AUTREP.GAf D.host.E n ≃* GfC Y :=
  MulEquiv.ofBijective (P.ψ.codRestrict (GfC Y) P.into)
    ⟨fun _ _ hab => P.inj (congrArg Subtype.val hab), fun g => by
      obtain ⟨h, hh⟩ := P.onto g.1 g.2
      exact ⟨h, Subtype.ext hh⟩⟩

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem exists_mem_isotL (hP : GlobalTheory.Published.HarishChandraFinite) {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) {s : ℕ} (hOk : A.fam.Ok s) (hC : GlobalTheory.Hk3.Core R F) (hM : MultEq R) (hX : Formalism.L2.DIV.GoodStable A.X) (hgen : ∀ χ ∈ A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (PY : principalLevelFrame.RowPsi (Yc D 0) n) (i : Fin D.R.m) (PW : principalLevelFrame.RowPsi (Wc D i) n) (hPY : GlobalTheory.StdFrame.StdPsi hF PY) (hPW : GlobalTheory.StdFrame.StdPsi hF PW) (π : Formalism.L2.NG.FinTyp D.host.E n) (hπ : π ∈ principalLevelFrame.OccRows R.θ PY (R.MY 0) (fun b => (levS _ (R.βY 0) (R.dat0 (R.levR F b)))) (fun b => (levChi _ (R.βY 0) (R.dat0 (R.levR F b)))) (fun _ => R.e0)) :
    ∃ w ∈ principalLevelFrame.isotL R.θ PW (R.MW i (sg0 D A))
      (levS _ (R.βW i) (R.datWp i (R.levL F false (sg0 D A))))
      (levChi _ (R.βW i) (R.datWp i (R.levL F false (sg0 D A))))
      (RealDat.eWf R i (sg0 D A)) π, w ≠ 0 := by
  classical
  obtain ⟨y, hyS, hy0, hyT, hyG⟩ := exists_good_vec R F hOk hC hX hgen PY π hπ
  obtain ⟨M₀, f, hf0, hfe, hfa⟩ := exists_conj_map R F PY π hπ
  obtain ⟨c, hc⟩ := hC.lev.βY 0 (lt_of_lt_of_le two_pos D.R.two_le_m)
  obtain ⟨c', hc'⟩ := hC.lev.βW i
  have hrk : (Yc D 0).rank = (Wc D i).rank := GlobalTheory.PartDims.rank_zeroth_component_eq.trans (GlobalTheory.PartDims.rank_weight_component_eq i).symm
  obtain ⟨j, Φ, hΦ⟩ := GlobalTheory.FinIsoExists.exists_isFinIso (Yc D 0) (Wc D i) (R.βY 0) (R.ΛY 0) _ (R.βW i) (R.ΛW i) _ R.Pg hrk hc hc'
    (GlobalTheory.T.typePlaces_not_pairwise_conjugate R.C.P R.Pg hC.lev.Pg)
  obtain ⟨h, hh⟩ := frames_inner (Yc D 0) (Wc D i) hF PY PW hPY hPW (by rw [GlobalTheory.PartDims.rank_zeroth_component_eq]; exact odd_r D.R) _ _ _ j Φ hΦ
  set P := R.levL F false (sg0 D A) with hPdef
  let e := eqv PY
  let σ : Representation ℂ (GfC (Yc D 0)) π.S := (GlobalTheory.OccRowVec.finRep π).comp e.symm.toMonoidHom
  have hσ : ∀ κ (x : π.S), σ (e κ) x = GlobalTheory.OccRowVec.finRep π κ x := fun κ x => by
    show GlobalTheory.OccRowVec.finRep π (e.symm (e κ)) x = _
    rw [MulEquiv.symm_apply_apply]
  have hirr : ∀ U : Submodule ℂ π.S, (∀ g, ∀ x ∈ U, σ g x ∈ U) → U = ⊥ ∨ U = ⊤ := fun U hU =>
    GlobalTheory.OccRowVec.finRep_irr π U fun g x hx => by rw [← hσ]; exact hU _ x hx
  have hy0' : (⟨y, hyS⟩ : π.S) ≠ 0 := fun h0 => hy0 (congrArg Subtype.val h0)
  haveI : Nontrivial π.S := ⟨⟨_, _, hy0'⟩⟩
  have hkill : (⟨y, hyS⟩ : π.S) ∈ killed σ (eqSet (Yc D 0) (R.βY 0) (R.dat0 R.triv) R.eG (RealDat.eC (A := A) D.what₂.embLL) P
      (∅ : Set Empty) Empty.elim Empty.elim Empty.elim) := by
    rw [mem_killed]
    rintro x ((⟨k, hk, rfl⟩ | ⟨κ, hκ, rfl⟩) | ⟨P0, -, -⟩)
    · obtain ⟨κ, rfl⟩ := e.surjective k
      rw [map_sub, Representation.asAlgebraHom_single, Representation.asAlgebraHom_single, LinearMap.sub_apply, one_smul, hσ,
        map_one, sub_eq_zero]
      exact Subtype.ext (hyT κ hk)
    · have := hyG (fun g => e.symm (κ g)) (fun g => by
        have e1 : PY.ψ (e.symm (κ g)) = (κ g : GA D (Yc D 0)) := congrArg Subtype.val (e.apply_symm_apply (κ g))
        rw [e1]; exact hκ g)
      rw [map_sub, map_sum, LinearMap.sub_apply, LinearMap.sum_apply, Representation.asAlgebraHom_single, map_one, one_smul, Module.End.one_apply, sub_eq_zero]
      apply Subtype.ext
      rw [Submodule.coe_sum]
      refine Eq.trans (Finset.sum_congr rfl fun g _ => ?_) this
      rw [Representation.asAlgebraHom_single]
      rfl
    · exact P0.elim
  have hfm : f ∈ homInto σ (finRep M₀) (allMaps R.θ M₀) := by
    refine ⟨hfa, fun g x => ?_⟩
    obtain ⟨κ, rfl⟩ := e.surjective g
    rw [hσ]
    exact hfe κ x
  haveI := GlobalTheory.PartDims.isTopologicalGroup_GA (Yc D 0)
  have hadm : GlobalTheory.PRep.IsAdmissible σ :=
    isAdmissible_of hirr hy0' (GlobalTheory.PartDims.isOpen_stab rfl rfl hkill) hfm hf0
      (fun K hK => GlobalTheory.CuspDec.finiteDimensional_fixed hP hC.models.inf K hK)
  have hgood := GlobalTheory.PartDims.isGoodRep_of_killed (ρ := σ) rfl rfl (GlobalTheory.DimFull.liftsY' hC)
    ((Submodule.ne_bot_iff _).2 ⟨_, hkill, hy0'⟩)
  have hmult := hM i M₀ j Φ hΦ π.S σ (isIrreducible_of hirr) hadm hgood
  obtain ⟨f', hf', hf0'⟩ : ∃ f' ∈ homInto σ ((finRep (R.MW i (sg0 D A))).comp Φ.toMulEquiv.toMonoidHom : Representation ℂ (GfC (Yc D 0)) _)
      (allMaps R.θ (R.MW i (sg0 D A))), f' ≠ 0 := by
    rw [← Submodule.ne_bot_iff, GlobalTheory.PartDims.homInto_comp]
    intro hb
    have h1 : cuspMult R.θ (R.MW i (sg0 D A)) (σ.comp Φ.symm.toMulEquiv.toMonoidHom) = 0 := by
      unfold cuspMult
      exact (Submodule.rank_eq_zero).2 hb
    rw [← hmult] at h1
    unfold cuspMult at h1
    rw [Submodule.rank_eq_zero] at h1
    rw [h1] at hfm
    exact hf0 hfm
  have hl := GlobalTheory.T.isometry_matches_parahoric_levels (Yc D 0) (Wc D i) (R.βY 0) (R.βW i) D.R.r D.R.t (r_le_Y 0) (r_le_rank_Wc i) R.Pg R.chi
    (fun _ _ => 1) j Φ hΦ
  have e4 : killed ((finRep (R.MW i (sg0 D A))).comp Φ.toMulEquiv.toMonoidHom : Representation ℂ (GfC (Yc D 0)) _)
        (eqSet (Yc D 0) (R.βY 0) (R.dat0 R.triv) R.eG (RealDat.eC (A := A) D.what₂.embLL) P (∅ : Set Empty) Empty.elim Empty.elim Empty.elim) =
      killed (finRep (R.MW i (sg0 D A))) (eqSet (Wc D i) (R.βW i) (R.datWp i R.triv) R.eG
        (RealDat.eC (A := A) D.what₂.embLL) P (∅ : Set Empty) Empty.elim Empty.elim Empty.elim) :=
    GlobalTheory.T.levelTypeHecke_killed_correspond_matching_iso (Yc D 0) (Wc D i) (R.βY 0) (R.βW i) D.R.r D.R.t (r_le_Y 0) (r_le_rank_Wc i) R.Pg R.chi (fun _ _ => 1) Φ R.eG _ P
      (∅ : Set Empty) Empty.elim Empty.elim Empty.elim _ _ hrk (fun κ => (hl κ).1) (fun κ => (hl κ).2) (fun P0 => P0.elim)
  have e2 : (R.Wat i (sg0 D A) P ⊓
      hPart (R.MW i (sg0 D A)) (levG _ (R.βW i) (R.datWp i R.triv)) (∅ : Set Empty) Empty.elim Empty.elim Empty.elim :
        Submodule ℂ (MMap (R.MW i (sg0 D A)))) =
      allMaps R.θ (R.MW i (sg0 D A)) ⊓ killed (finRep (R.MW i (sg0 D A))) (eqSet (Wc D i) (R.βW i) (R.datWp i R.triv) R.eG
        (RealDat.eC (A := A) (sg0 D A)) P (∅ : Set Empty) Empty.elim Empty.elim Empty.elim) :=
    GlobalTheory.T.goodForms_eq_killed_by_groupAlgebra R.θ (R.MW i (sg0 D A)) (R.βW i) (R.datWp i R.triv) R.eG _ P (∅ : Set Empty) Empty.elim Empty.elim Empty.elim rfl rfl
      (GlobalTheory.DimFull.liftsW' hC i)
  have e3 : RealDat.eC (A := A) (sg0 D A) = RealDat.eC (A := A) D.what₂.embLL := by rw [GlobalTheory.PartDims.sign_at_base_place_eq_embedding R]
  have hw : f' ⟨y, hyS⟩ ∈ R.Wat i (sg0 D A) P := by
    have h1 := killed_map hf'.2 hkill
    rw [e4, ← e3] at h1
    exact (e2.ge ⟨hf'.1 _, h1⟩).1
  let Ψ : π.S →ₗ[ℂ] MMap (R.MW i (sg0 D A)) := f' ∘ₗ GlobalTheory.OccRowVec.finRep π h⁻¹
  have hΨe : principalLevelFrame.IsEqvA (principalLevelFrame.actM PW (R.MW i (sg0 D A))) π Ψ := by
    intro κ x
    have h1 := hf'.2 (e (h⁻¹ * κ * h)) (GlobalTheory.OccRowVec.finRep π h⁻¹ x)
    rw [hσ, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_right, map_mul, Module.End.mul_apply] at h1
    refine Eq.trans h1 ?_
    have h2 := hh (h⁻¹ * κ * h)
    rw [show h * (h⁻¹ * κ * h) * h⁻¹ = κ by group] at h2
    refine MultilinearMap.ext fun v => funext fun g => ?_
    rw [principalLevelFrame.actM_apply, ← h2]
    rfl
  have hΨr : LinearMap.range Ψ ≤ principalLevelFrame.Minf R.θ PW (R.MW i (sg0 D A)) := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨N, hN, hfix⟩ := π.smooth x x.2
    obtain ⟨N, rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    refine Submodule.mem_iSup_of_mem N (Submodule.subset_span ?_)
    have h1 := (GlobalTheory.MultMem.mem_mult_iff ..).1 (hf'.1 (GlobalTheory.OccRowVec.finRep π h⁻¹ x))
    refine ⟨h1.aut, h1.cusp, ?_, h1.equiv, h1.cont⟩
    rintro v _ ⟨κ, hκ, rfl⟩ g
    have h2 := hΨe κ x
    rw [show (⟨Formalism.L2.NG.rt D.host.E n κ x, π.stable κ x x.2⟩ : π.S) = x from Subtype.ext (hfix κ hκ)] at h2
    rw [one_mul]
    exact (congrArg (fun T : MMap (R.MW i (sg0 D A)) => T v g) h2).symm
  refine ⟨f' ⟨y, hyS⟩, ⟨hw, ?_⟩, fun h0 => hy0' (injective_of hirr hf'.2 hf0' (h0.trans (map_zero _).symm))⟩
  refine Submodule.mem_iSup_of_mem Ψ (Submodule.mem_iSup_of_mem ⟨hΨe, hΨr⟩ ⟨GlobalTheory.OccRowVec.finRep π h ⟨y, hyS⟩, ?_⟩)
  show f' (GlobalTheory.OccRowVec.finRep π h⁻¹ (GlobalTheory.OccRowVec.finRep π h ⟨y, hyS⟩)) = _
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem isot_ne_bot : GlobalTheory.Published.HarishChandraFinite → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → GlobalTheory.CuspMult.MultEq R.toRealDat → Formalism.L2.DIV.GoodStable A3.A.X → (∀ χ ∈ A3.A.X, chiIdem χ * lvlIdem F.P0 F.ψ0 ≠ 0) → ∀ (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : RecTie.TopMultH R.toRealDat) (hinj : ∀ i t, Function.Injective (R.toRealDat.extV i t)) (X0 : BaseLevelRowSide D) (Ish : RecTie.RowIds (RowSide.sharp D) (RecTie.toChainReal R.toRealDat F.lv2 tupT hm hTop) true) (Ib : RecTie.RowIds X0.s (RecTie.toChainReal R.toRealDat F.lv2 tupT hm hTop) false) (IL : RecTie.LiftIds (RecTie.toLiftReal R.toRealDat F.lv2 tupT hm hTop hinj)) (Kc : RecTie.ColReal D) {Xd : DivX D} (E : EigIdx D Xd) (labPi : E.Pi → A3.A.fam.base.Ix) {n : ℕ} (PY : principalLevelFrame.RowPsi (Yc D 0) n) (PW : ∀ i, principalLevelFrame.RowPsi (Wc D i) n) eFT piOf ι nch Tp, RecTie.RecReal R.toRealDat F.lv2 tupT hm hTop hinj X0 Ish Ib IL Kc E labPi PY PW eFT piOf ι nch Tp → tupT D.what₂.mu0 = A3.A.μ0 → ∀ (hF : D.host.F = maximalRealSubfield D.host.E), GlobalTheory.StdFrame.StdPsi hF PY → (∀ i, GlobalTheory.StdFrame.StdPsi hF (PW i)) → ∀ σ (i : Fin D.R.m), D.what₂.isot ((i : ℕ) + 1) (D.what₂.ft σ) ≠ ⊥ := by
  intro hP D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hChar hEx hME hGS hgen tupT hm hTop hinj X0 Ish Ib IL Kc Xd E labPi n PY PW eFT piOf ι nch Tp hRec hmu hF hPY hPW σ i
  have hL := hRec.tied.lift
  obtain ⟨w, hw, hw0⟩ := exists_mem_isotL hP R.toRealDat F.lv2 hOk.ok2 (GlobalTheory.CoreOfWeak.core_of_weak R F hChar hEx).1 hME hGS hgen hF PY i (PW i)
    hPY (hPW i) (principalLevelFrame.rowRepR R.θ (eFT (D.what₂.ft σ))) (principalLevelFrame.rowRepR_occ _ _)
  intro hbot
  let L := RecTie.toLiftReal R.toRealDat F.lv2 tupT hm hTop hinj
  let lw : L.AmbW i := (PiTensorProduct.lift : Mult.MMap (R.MW i (sg0 D A3.A)) ≃ₗ[ℂ] L.AmbW i) w
  have hgood : lw ∈ L.Wc i := Submodule.mem_map_of_mem hw.1
  let y : D.what₂.Mj ((i : ℕ) + 1) := (IL.jMj i).symm ⟨lw, hgood⟩
  have hjy : ((IL.jMj i y : L.Wc i) : L.AmbW i) = lw := by
    simp only [y, LinearEquiv.apply_symm_apply]
  have hmem : ((IL.jMj i y : L.Wc i) : L.AmbW i) ∈ IL.prtW i (D.what₂.ft σ) := by
    rw [hjy, hRec.prtWE]
    exact ⟨w, hw, rfl⟩
  have hy0 : y ∈ D.what₂.isot ((i : ℕ) + 1) (D.what₂.ft σ) := (hL.isot i _ y).2 hmem
  rw [hbot, Submodule.mem_bot] at hy0
  apply hw0
  have h1 : lw = 0 := by rw [← hjy, hy0, map_zero]; rfl
  exact (PiTensorProduct.lift : Mult.MMap (R.MW i (sg0 D A3.A)) ≃ₗ[ℂ] L.AmbW i).injective (h1.trans (map_zero _).symm)

end GlobalTheory.KapIsot
end
