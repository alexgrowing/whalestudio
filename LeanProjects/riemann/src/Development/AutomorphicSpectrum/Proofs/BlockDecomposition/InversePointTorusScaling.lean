import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralSiegelConeInvModulusLtTopWeilStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelDomainReduction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CutPMulCutP
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsArchEquivEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProjArchOfInfEmbArchPi
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open NumberField IsDedekindDomain Matrix

noncomputable section
namespace GlobalTheory.CompanionTheory.TorusCoord

variable {K : Type} [CommRing K] {n r : ℕ} {X Y : Matrix (Fin n) (Fin r) K} {Rx Ry : Matrix (Fin r) (Fin n) K}

theorem left_proj (h1 : Rx * X = 0) (h3 : Rx * Y = 1) : Rx * (1 - X * Ry - Y * Rx) = 0 := by
  simp only [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, h1, h3, Matrix.zero_mul, Matrix.one_mul, sub_zero,
    sub_self]

theorem left_proj' (h2 : Ry * Y = 0) (h4 : Ry * X = 1) : Ry * (1 - X * Ry - Y * Rx) = 0 := by
  simp only [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, h2, h4, Matrix.zero_mul, Matrix.one_mul, sub_zero,
    sub_self]

theorem lin (h1 : Rx * X = 0) (h2 : Ry * Y = 0) (h3 : Rx * Y = 1) (h4 : Ry * X = 1)
    {A B : Matrix (Fin n) (Fin n) K} (hAB : A * B = 1) {T S : Matrix (Fin r) (Fin r) K} (hTS : T * S = 1)
    (hST : S * T = 1) (hX : B * X = X * T) (hY : B * Y = Y * S) (ξ : Matrix (Fin n) (Fin 1) K)
    (hq : B * ((1 - X * Ry - Y * Rx) * ξ) = (1 - X * Ry - Y * Rx) * ξ) :
    Ry * (A * ξ) = S * (Ry * ξ) ∧ Rx * (A * ξ) = T * (Rx * ξ) ∧
      (1 - X * Ry - Y * Rx) * (A * ξ) = (1 - X * Ry - Y * Rx) * ξ := by
  have hRxQ := left_proj (Ry := Ry) h1 h3
  have hRyQ := left_proj' (Rx := Rx) h2 h4
  have e : ∀ {m : ℕ} (M : Matrix (Fin n) (Fin m) K),
      (1 - X * Ry - Y * Rx) * M = M - X * (Ry * M) - Y * (Rx * M) := fun M => by
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
  generalize hQ : 1 - X * Ry - Y * Rx = Q at hq hRxQ hRyQ ⊢
  have eQ : ∀ {m : ℕ} (M : Matrix (Fin n) (Fin m) K), Q * M = M - X * (Ry * M) - Y * (Rx * M) := fun M => by
    rw [← hQ]; exact e M
  have hAX : A * X = X * S := by
    have h : A * (B * X) = X := by rw [← Matrix.mul_assoc, hAB, Matrix.one_mul]
    rw [hX, ← Matrix.mul_assoc] at h
    calc A * X = A * X * (T * S) := by rw [hTS, Matrix.mul_one]
      _ = (A * X * T) * S := by simp only [Matrix.mul_assoc]
      _ = X * S := by rw [h]
  have hAY : A * Y = Y * T := by
    have h : A * (B * Y) = Y := by rw [← Matrix.mul_assoc, hAB, Matrix.one_mul]
    rw [hY, ← Matrix.mul_assoc] at h
    calc A * Y = A * Y * (S * T) := by rw [hST, Matrix.mul_one]
      _ = (A * Y * S) * T := by simp only [Matrix.mul_assoc]
      _ = Y * T := by rw [h]
  have hAQ : A * (Q * ξ) = Q * ξ := by
    conv_lhs => rw [← hq]
    rw [← Matrix.mul_assoc, hAB, Matrix.one_mul]
  have hQX : Q * X = 0 := by rw [eQ, h1, h4]; simp
  have hQY : Q * Y = 0 := by rw [eQ, h2, h3]; simp
  have hQQ : Q * Q = Q := by rw [eQ, hRxQ, hRyQ]; simp
  have hdec : ξ = X * (Ry * ξ) + Y * (Rx * ξ) + Q * ξ := by rw [eQ]; abel
  have hu : A * ξ = X * (S * (Ry * ξ)) + Y * (T * (Rx * ξ)) + Q * ξ := by
    conv_lhs => rw [hdec]
    rw [Matrix.mul_add, Matrix.mul_add, hAQ, ← Matrix.mul_assoc A X, ← Matrix.mul_assoc A Y, hAX, hAY,
      Matrix.mul_assoc, Matrix.mul_assoc]
  rw [hu]
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.mul_add, Matrix.mul_add, ← Matrix.mul_assoc Ry X, ← Matrix.mul_assoc Ry Y, ← Matrix.mul_assoc Ry Q, h4, h2,
      hRyQ]
    simp
  · rw [Matrix.mul_add, Matrix.mul_add, ← Matrix.mul_assoc Rx X, ← Matrix.mul_assoc Rx Y, ← Matrix.mul_assoc Rx Q, h3, h1,
      hRxQ]
    simp
  · rw [Matrix.mul_add, Matrix.mul_add, ← Matrix.mul_assoc Q X, ← Matrix.mul_assoc Q Y, ← Matrix.mul_assoc Q Q, hQX, hQY,
      hQQ]
    simp

theorem mt_inv_mul {D : D7} (V : HSp D) (a : GA D V) : Formalism.L2.Theta.mt V a⁻¹ * Formalism.L2.Theta.mt V a = 1 := by
  have h := congrArg Units.val (map_mul (Formalism.L2.Theta.matHom V) a⁻¹ a)
  rw [inv_mul_cancel, map_one] at h
  exact h.symm

theorem map_mt_eq_archMat {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (V : HSp D) (ρ : D.what₂.Tau) (a : GA D V) :
    (Formalism.L2.Theta.mt V a).map (fun x => θ ρ (infPart D x)) =
      GlobalTheory.Orb.archMat D.sp.cm.sig V.gram (embOverOf D ρ) (projArch D.sp.cm.sig V.gram (placeOf D ρ) a) := by
  have e := eq_infProj hθ (embOverOf D ρ) rfl
  have h := infMat_infProj (J := V.gram) (isCMExt_host D) (embOverOf D ρ) a
  rw [← e] at h
  refine Eq.trans ?_ (h.trans (GlobalTheory.Orb.archMat_eq_archEquiv V.gram (isCMExt_host D) _ _).symm)
  ext i j
  rfl

theorem torus_coords : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) {r : ℕ} (Xf Yf : Matrix (Fin V.rank) (Fin r) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram Xf Yf → ∀ (t : Fin r → ℝ), (∀ i, 0 < t i) → ∀ (a : GA D V), GlobalTheory.SiegelSet.IsTorusElt D.sp.cm.sig V.gram Xf Yf t a → ∀ (ξ : Matrix (Fin V.rank) (Fin 1) D.host.E), (invPt V a ξ).map (finPart D) = ξ.map (fun x => (1 : Af D.host.F) ⊗ₜ[D.host.F] x) ∧ ∀ ρ, (((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram).map (tauE D ρ)) * compAt θ ρ (invPt V a ξ) = diagonal (fun i => ((t i : ℂ))⁻¹) * ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) * ξ).map (tauE D ρ)) ∧ (((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram).map (tauE D ρ)) * compAt θ ρ (invPt V a ξ) = diagonal (fun i => (t i : ℂ)) * ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram) * ξ).map (tauE D ρ)) ∧ (((1 - Xf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) - Yf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram)).map (tauE D ρ)) * compAt θ ρ (invPt V a ξ) = ((1 - Xf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) - Yf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram)) * ξ).map (tauE D ρ)) := by
  intro D θ hθ V r Xf Yf hW t ht a ha ξ
  have hcm := isCMExt_host D
  have hJ := isHermND_gram V
  refine ⟨?_, fun ρ => ?_⟩
  · have h1 : (Formalism.L2.Theta.mt V a⁻¹).map (finPart D) = 1 :=
      GlobalTheory.CompanionTheory.SiegelArch.map_matHom_fin V.gram (inv_mem ha.1)
    change (HMul.hMul (Formalism.L2.Theta.mt V a⁻¹) (ξ.map (incA D))).map (finPart D) = _
    rw [Matrix.map_mul, h1, Matrix.one_mul, Matrix.map_map]
    ext i j
    exact GlobalTheory.LatVac.finPart_incA _
  · have hhτ : ∀ x, θ ρ (infPart D (incA D x)) = tauE D ρ x := fun x => (hθ ρ).1 x
    let φ : AE D →+* ℂ := (θ ρ).comp (infPart D)
    have hAB : (Formalism.L2.Theta.mt V a⁻¹).map φ * (Formalism.L2.Theta.mt V a).map φ = 1 := by
      rw [← Matrix.map_mul, mt_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    have hB : (Formalism.L2.Theta.mt V a).map φ = _ := map_mt_eq_archMat hθ V ρ a
    have hcomp : compAt θ ρ (invPt V a ξ) = (Formalism.L2.Theta.mt V a⁻¹).map φ * ξ.map (tauE D ρ) := by
      change (HMul.hMul (Formalism.L2.Theta.mt V a⁻¹) (ξ.map (incA D))).map φ = _
      rw [Matrix.map_mul, Matrix.map_map]
      congr 1
      ext i j
      exact hhτ _
    obtain ⟨hX, hY, hZ⟩ := ha.2 (placeOf D ρ) (embOverOf D ρ)
    rw [← hB] at hX hY hZ
    simp only [embOverOf_val] at hX hY hZ
    obtain ⟨-, -, hxy⟩ := GlobalTheory.CentreFin.frame_emb hcm hW (tauE D ρ)
    have hxx := (GlobalTheory.CentreFin.frame_emb hcm hW (tauE D ρ)).1
    have hyy := (GlobalTheory.CentreFin.frame_emb hcm hW (tauE D ρ)).2.1
    have hJc : (V.gram.map (tauE D ρ))ᴴ = V.gram.map (tauE D ρ) := by
      ext i j
      rw [conjTranspose_apply, Matrix.map_apply, Matrix.map_apply, ← hcm.2.2.2, hJ.1]
    have hyx := GlobalTheory.CentreFin.dual_swap hJc hxy
    have hR : ∀ C : Matrix (Fin V.rank) (Fin r) D.host.E,
        (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram).map (tauE D ρ) =
          (C.map (tauE D ρ))ᴴ * V.gram.map (tauE D ρ) := fun C => by
      rw [Matrix.map_mul, GlobalTheory.CentreFin.map_cT_emb hcm]
    have h1 : ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram).map (tauE D ρ)) * Xf.map (tauE D ρ) = 0 := by
      rw [hR]; exact hxx
    have h2 : ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram).map (tauE D ρ)) * Yf.map (tauE D ρ) = 0 := by
      rw [hR]; exact hyy
    have h3 : ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram).map (tauE D ρ)) * Yf.map (tauE D ρ) = 1 := by
      rw [hR]; exact hxy
    have h4 : ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram).map (tauE D ρ)) * Xf.map (tauE D ρ) = 1 := by
      rw [hR]; exact hyx
    have h4E : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) * Xf = 1 := by
      refine Matrix.map_injective (tauE D ρ).injective ?_
      beta_reduce
      rw [Matrix.map_mul, h4, Matrix.map_one _ (map_zero _) (map_one _)]
    have hQm : (1 - Xf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) -
          Yf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram)).map (tauE D ρ) =
        1 - Xf.map (tauE D ρ) * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram).map (tauE D ρ) -
          Yf.map (tauE D ρ) * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram).map (tauE D ρ) := by
      change (tauE D ρ).mapMatrix _ = _
      rw [map_sub, map_sub, map_one]
      simp only [RingHom.mapMatrix_apply, Matrix.map_mul]
    have hxq := left_proj (X := Xf) (Y := Yf) (Rx := Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram)
      (Ry := Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) hW.xx hW.xy
    have hyq := left_proj' (X := Xf) (Y := Yf) (Rx := Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram)
      (Ry := Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) hW.yy h4E
    have hq := hZ (fun i => ((1 - Xf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) -
          Yf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram)) * ξ :
            Matrix (Fin V.rank) (Fin 1) D.host.E) i 0)
      (by
        funext i
        have e : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram) * ((1 - Xf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) -
          Yf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram)) * ξ) = 0 := by
          rw [← Matrix.mul_assoc, hxq, Matrix.zero_mul]
        exact congrFun (congrFun e i) 0)
      (by
        funext i
        have e : (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) * ((1 - Xf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Yf * V.gram) -
          Yf * (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) Xf * V.gram)) * ξ) = 0 := by
          rw [← Matrix.mul_assoc, hyq, Matrix.zero_mul]
        exact congrFun (congrFun e i) 0)
    have hq' := by
      refine lin h1 h2 h3 h4 hAB (T := diagonal fun i => (t i : ℂ)) (S := diagonal fun i => (t i : ℂ)⁻¹) ?_ ?_ hX hY
        (ξ.map (tauE D ρ)) ?_
      · rw [diagonal_mul_diagonal, ← diagonal_one]
        congr 1; funext i
        exact mul_inv_cancel₀ (by exact_mod_cast (ht i).ne')
      · rw [diagonal_mul_diagonal, ← diagonal_one]
        congr 1; funext i
        exact inv_mul_cancel₀ (by exact_mod_cast (ht i).ne')
      · rw [← hQm, ← Matrix.map_mul]
        ext i j
        obtain rfl : j = 0 := Subsingleton.elim _ _
        exact congrFun hq i
    obtain ⟨c1, c2, c3⟩ := hq'
    have m : ∀ {a : ℕ} (M : Matrix (Fin a) (Fin V.rank) D.host.E),
        (M * ξ).map (tauE D ρ) = M.map (tauE D ρ) * ξ.map (tauE D ρ) := fun M => Matrix.map_mul
    rw [hcomp, m, m, m, hQm]
    exact ⟨c1, c2, c3⟩

end GlobalTheory.CompanionTheory.TorusCoord
