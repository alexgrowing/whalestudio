import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FramedDConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPairApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuumEquationsInArchimedeanDarbouxCoordinat

noncomputable section

open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.VacLn
open GlobalTheory.HoweD GlobalTheory.VacBridge

namespace GlobalTheory.HoweD

theorem exists_bridgeD : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (α β κ : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : InfinitePlace F → ℕ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ) (ε : InfinitePlace F → ℤˣ), IsCMExt F E σ → FramedD τ JA JB a b A C →
    ∃ (J e : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
        ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)))
      (e' : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F)),
      (∀ y, J (J y) = -y) ∧ (∀ y, e (e y) = e y) ∧ (∀ y, J (e y) = e (J y)) ∧ (∀ y, (e y).1 = e' y.1) ∧
      (∀ y x, trPair F κ x (e y).2 = trPair F κ (e' x) y.2) ∧
      ∀ y, ∃ (u u' u₁ : Matrix α β (AE F E)) (c : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ),
        At (evI F) u ∧ At (evI F) u' ∧ At (evI F) u₁ ∧ (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) ∧
        (∀ w, u'.map (piInf (τ w)) = A w * ((((ε w : ℤ) : ℂ) * Complex.I) • (Jm (P w) (Q w) * c w * Jm (R w) (S w))) * (C w)ᵀ) ∧
        (∀ w, u₁.map (piInf (τ w)) = A w * (Complex.I • (Jm (P w) (Q w) * c w * Jm (R w) (S w))) * (C w)ᵀ) ∧
        coord d u = y ∧ coord d u' = J (y - (2 : ℝ) • e y) ∧ coord d u₁ = J y := by
  intro F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S τ JA JB d a b A C ε hcm hfr
  have := hcm.1
  obtain ⟨-, hA, hC⟩ := hfr
  choose IA hIA using fun w =>
    frame_inv _ (A w) (Jm (P w) (Q w)) (jm_mul_self (P w) (Q w)) (hA w).1 (hA w).2
  choose IC hIC using fun w =>
    frame_inv _ (C w) (Jm (R w) (S w)) (jm_mul_self (R w) (S w)) (hC w).1 (hC w).2
  have hback : ∀ w (X : Matrix α β ℂ), A w * (IA w * X * (IC w)ᵀ) * (C w)ᵀ = X := by
    intro w X
    have hCt : (IC w)ᵀ * (C w)ᵀ = 1 := by rw [← Matrix.transpose_mul, (hIC w).2, Matrix.transpose_one]
    calc _ = (A w * IA w) * X * ((IC w)ᵀ * (C w)ᵀ) := by simp only [Matrix.mul_assoc]
      _ = X := by rw [(hIA w).2, hCt, Matrix.one_mul, Matrix.mul_one]
  have hfwd : ∀ w (c : Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ), IA w * (A w * c * (C w)ᵀ) * (IC w)ᵀ = c := by
    intro w c
    have hCt : (C w)ᵀ * (IC w)ᵀ = 1 := by rw [← Matrix.transpose_mul, (hIC w).1, Matrix.transpose_one]
    calc _ = (IA w * A w) * c * ((C w)ᵀ * (IC w)ᵀ) := by simp only [Matrix.mul_assoc]
      _ = c := by rw [(hIA w).1, hCt, Matrix.one_mul, Matrix.mul_one]
  let Ψl : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
      (∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) :=
    { toFun := fun y w => IA w * (mkD d y).map (piInf (τ w)) * (IC w)ᵀ
      map_add' := fun y y' => by
        funext w
        simp only [mkD_add, Pi.add_apply]
        rw [Matrix.map_add _ (map_add _), Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun r y => by
        funext w
        simp only [mkD_smul_real, map_smul_piInf, ext_realAd, RingHom.id_apply, Pi.smul_apply]
        rw [Matrix.mul_smul, Matrix.smul_mul]
        ext i j
        simp [Complex.real_smul] }
  have hΨl : ∀ y w, A w * Ψl y w * (C w)ᵀ = (mkD d y).map (piInf (τ w)) := fun y w => hback w _
  have hinj : Function.Injective Ψl := by
    intro y y' h
    have hu : mkD d y = mkD d y' := eq_of_at_map σ hcm τ (at_mkD d y) (at_mkD d y') fun w => by
      rw [← hΨl, ← hΨl, h]
    rw [← coord_mkD d y, ← coord_mkD d y', hu]
  have hsurj : Function.Surjective Ψl := by
    intro c
    obtain ⟨u, hu, hM⟩ := exists_at_map σ hcm τ (fun w => A w * c w * (C w)ᵀ)
    refine ⟨coord d u, funext fun w => ?_⟩
    show IA w * (mkD d (coord d u)).map (piInf (τ w)) * (IC w)ᵀ = c w
    rw [mkD_coord d hu, hM w, hfwd]
  let Ψ := LinearEquiv.ofBijective Ψl ⟨hinj, hsurj⟩
  let L : (∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) →ₗ[ℝ]
      (∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) :=
    { toFun := fun c w => Complex.I • (Jm (P w) (Q w) * c w * Jm (R w) (S w))
      map_add' := fun c c' => by
        funext w
        simp only [Pi.add_apply, Matrix.mul_add, Matrix.add_mul, smul_add]
      map_smul' := fun r c => by
        funext w
        simp only [Pi.smul_apply, RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul]
        exact smul_comm _ _ _ }
  let Pm : (∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) →ₗ[ℝ]
      (∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) :=
    { toFun := fun c w => (if ε w = -1 then (1 : ℂ) else 0) • c w
      map_add' := fun c c' => by
        funext w
        simp only [Pi.add_apply, smul_add]
      map_smul' := fun r c => by
        funext w
        simp only [Pi.smul_apply, RingHom.id_apply]
        exact smul_comm _ _ _ }
  have hLL : ∀ c, L (L c) = -c := by
    intro c
    funext w
    show Complex.I • (Jm (P w) (Q w) * (Complex.I • (Jm (P w) (Q w) * c w * Jm (R w) (S w))) * Jm (R w) (S w)) = -c w
    have key : Jm (P w) (Q w) * (Jm (P w) (Q w) * c w * Jm (R w) (S w)) * Jm (R w) (S w) = c w := by
      calc _ = (Jm (P w) (Q w) * Jm (P w) (Q w)) * c w * (Jm (R w) (S w) * Jm (R w) (S w)) := by
            simp only [Matrix.mul_assoc]
        _ = c w := by rw [jm_mul_self, jm_mul_self, Matrix.one_mul, Matrix.mul_one]
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul, key, Complex.I_mul_I, neg_one_smul]
  have hLP : ∀ c, L (Pm c) = Pm (L c) := by
    intro c
    funext w
    show Complex.I • (Jm (P w) (Q w) * ((if ε w = -1 then (1 : ℂ) else 0) • c w) * Jm (R w) (S w)) =
      (if ε w = -1 then (1 : ℂ) else 0) • (Complex.I • (Jm (P w) (Q w) * c w * Jm (R w) (S w)))
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_comm]
  let tm : AF F := ((fun w => if ε w = -1 then 1 else 0 : InfiniteAdeleRing F), 0)
  have htm : tm * tm = tm := by
    refine Prod.ext (funext fun w => ?_) ?_
    · show (if ε w = -1 then (1 : w.Completion) else 0) * (if ε w = -1 then 1 else 0) = if ε w = -1 then 1 else 0
      split_ifs <;> simp
    · show (0 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) * 0 = 0
      exact mul_zero _
  have htt : evI F tm * evI F tm = evI F tm := by rw [← evI_mul, htm]
  have hext : ∀ w, InfinitePlace.Completion.extensionEmbedding w (tm.1 w) = if ε w = -1 then 1 else 0 := by
    intro w
    show InfinitePlace.Completion.extensionEmbedding w (if ε w = -1 then (1 : w.Completion) else 0) = _
    split_ifs <;> simp
  have hΨe : ∀ y, Ψl (mulP (evI F tm) y) = Pm (Ψl y) := by
    intro y
    funext w
    show IA w * (mkD d (mulP (evI F tm) y)).map (piInf (τ w)) * (IC w)ᵀ =
      (if ε w = -1 then (1 : ℂ) else 0) • (IA w * (mkD d y).map (piInf (τ w)) * (IC w)ᵀ)
    rw [mkD_mulP, map_smul_piInf, hext, Matrix.mul_smul, Matrix.smul_mul]
  let J : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
      ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) :=
    (Ψ.symm : (∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) →ₗ[ℝ] _).comp (L.comp Ψl)
  have hΨJ : ∀ y, Ψl (J y) = L (Ψl y) := fun y => Ψ.apply_symm_apply _
  refine ⟨J, mulP (evI F tm), mulC (evI F tm), ?_, ?_, ?_, fun y => rfl, ?_, ?_⟩
  · intro y
    apply hinj
    rw [hΨJ, hΨJ, hLL, map_neg]
  · intro y
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · show evI F tm * (evI F tm * y.1 i) = evI F tm * y.1 i
      rw [← mul_assoc, htt]
    · show evI F tm * (evI F tm * y.2 i) = evI F tm * y.2 i
      rw [← mul_assoc, htt]
  · intro y
    apply hinj
    rw [hΨJ, hΨe, hΨe, hΨJ, hLP]
  · intro y x
    simp only [trPair_apply]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    show x i * (evI F tm * y.2 i) = (evI F tm * x i) * y.2 i
    ring
  · intro y
    refine ⟨mkD d y, mkD d (J (y - (2 : ℝ) • mulP (evI F tm) y)), mkD d (J y), Ψl y, at_mkD d _, at_mkD d _,
      at_mkD d _, fun w => (hΨl y w).symm, fun w => ?_, fun w => ?_, coord_mkD d _, coord_mkD d _, coord_mkD d _⟩
    · rw [← hΨl, hΨJ, map_sub, map_smul, hΨe]
      show A w * (Complex.I • (Jm (P w) (Q w) * (Ψl y w - (2 : ℝ) • ((if ε w = -1 then (1 : ℂ) else 0) • Ψl y w)) *
          Jm (R w) (S w))) * (C w)ᵀ =
        A w * ((((ε w : ℤ) : ℂ) * Complex.I) • (Jm (P w) (Q w) * Ψl y w * Jm (R w) (S w))) * (C w)ᵀ
      congr 2
      generalize Ψl y w = X
      rcases Int.units_eq_one_or (ε w) with h1 | h1
      · rw [h1, if_neg (by decide)]
        simp
      · rw [h1, if_pos rfl, one_smul, two_smul, sub_add_cancel_left]
        simp [Matrix.mul_neg, Matrix.neg_mul]
    · rw [← hΨl, hΨJ]
      rfl

end GlobalTheory.HoweD

end
