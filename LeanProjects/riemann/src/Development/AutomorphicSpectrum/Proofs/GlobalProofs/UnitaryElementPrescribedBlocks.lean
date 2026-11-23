import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsAdaptedEmpty
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LanglandsDecompositionUnipotentLevi
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces
import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.RealPtExHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousKapSymm
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section
namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore

def compHom {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (τ : D.what₂.Tau) :
    AF D.host.F ⊗[D.host.F] D.host.E →+* ℂ := (θ τ).comp (infPart D)

theorem adele_ext {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} (hθ : IsInfFam θ)
    {a b : AF D.host.F ⊗[D.host.F] D.host.E} (hf : finPart D a = finPart D b)
    (hc : ∀ τ, compHom θ τ a = compHom θ τ b) : a = b := by
  obtain ⟨w, -, hw⟩ := Formalism.IndefR.Mi.realPtEx_holds (D := D) θ 1 1 hθ (fun _ _ _ => 0)
  have h0 : ∀ c : AF D.host.F ⊗[D.host.F] D.host.E, finPart D c = 0 → (∀ τ, compHom θ τ c = 0) → c = 0 := by
    intro c h1 h2
    have e1 : (Matrix.of fun _ _ => c : Matrix (Fin 1) (Fin 1) _) = w := hw _ ⟨by
      ext i j
      exact h1, fun τ => by
      ext i j
      exact h2 τ⟩
    have e2 : (0 : Matrix (Fin 1) (Fin 1) (AF D.host.F ⊗[D.host.F] D.host.E)) = w := hw _ ⟨by
      ext i j
      exact map_zero (finPart D), fun τ => by
      ext i j
      exact map_zero (compHom θ τ)⟩
    exact congrFun (congrFun (e1.trans e2.symm) 0) 0
  refine sub_eq_zero.1 (h0 _ ?_ fun τ => ?_)
  · rw [map_sub, hf, sub_self]
  · rw [map_sub, hc, sub_self]

theorem compHom_adMat {D : D7} {a b : ℕ} (τ : D.what₂.Tau) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (hθ : IsInfFam θ) (Y : Matrix (Fin a) (Fin b) D.host.E) :
    (adMat D.host.F Y).map (compHom θ τ) = Y.map (tauE D τ) := by
  ext i j
  have : infPart D ((1 : AF D.host.F) ⊗ₜ[D.host.F] Y i j) = (1 : Ainf D.host.F) ⊗ₜ[D.host.F] Y i j := by
    simp [infPart]
  simp only [Matrix.map_apply, adMat, compHom, RingHom.comp_apply]
  show θ τ (infPart D ((1 : AF D.host.F) ⊗ₜ[D.host.F] Y i j)) = _
  rw [this]
  exact (hθ τ).1 _

theorem map_one_add_of {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {n a b : ℕ}
    (P : Matrix (Fin n) (Fin a) A) (Q : Matrix (Fin a) (Fin n) A) (R : Matrix (Fin n) (Fin b) A) (S : Matrix (Fin b) (Fin n) A)
    {p : Matrix (Fin n) (Fin a) B} {q : Matrix (Fin a) (Fin n) B} {r : Matrix (Fin n) (Fin b) B} {s : Matrix (Fin b) (Fin n) B}
    (hp : P.map φ = p) (hq : Q.map φ = q) (hr : R.map φ = r) (hs : S.map φ = s) :
    (1 + P * Q + R * S).map φ = 1 + p * q + r * s := by
  subst hp hq hr hs
  rw [Matrix.map_add _ (map_add φ), Matrix.map_add _ (map_add φ), Matrix.map_one _ (map_zero φ) (map_one φ), Matrix.map_mul, Matrix.map_mul]

theorem map_one_add_of_zero {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {n a b : ℕ}
    (P : Matrix (Fin n) (Fin a) A) (Q : Matrix (Fin a) (Fin n) A) (R : Matrix (Fin n) (Fin b) A) (S : Matrix (Fin b) (Fin n) A)
    (hq : Q.map φ = 0) (hr : R.map φ = 0) : (1 + P * Q + R * S).map φ = 1 := by
  rw [map_one_add_of φ P Q R S rfl hq hr rfl, Matrix.mul_zero, Matrix.zero_mul, add_zero, add_zero]

theorem matrix_ext_parts {D : D7} {n : ℕ} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} (hθ : IsInfFam θ)
    (M N : Matrix (Fin n) (Fin n) (AF D.host.F ⊗[D.host.F] D.host.E))
    (hf : M.map (finPart D) = N.map (finPart D)) (hc : ∀ τ, M.map (compHom θ τ) = N.map (compHom θ τ)) : M = N := by
  ext i j
  exact adele_ext hθ (congrFun (congrFun hf i) j) fun τ => congrFun (congrFun (hc τ) i) j

theorem map_compHom_mul {D : D7} {a b c : ℕ} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (τ : D.what₂.Tau)
    (A : Matrix (Fin a) (Fin b) (AF D.host.F ⊗[D.host.F] D.host.E)) (B : Matrix (Fin b) (Fin c) (AF D.host.F ⊗[D.host.F] D.host.E)) :
    (A * B).map (compHom θ τ) = A.map (compHom θ τ) * B.map (compHom θ τ) := Matrix.map_mul

theorem map_finPart_mul {D : D7} {a b c : ℕ}
    (A : Matrix (Fin a) (Fin b) (AF D.host.F ⊗[D.host.F] D.host.E)) (B : Matrix (Fin b) (Fin c) (AF D.host.F ⊗[D.host.F] D.host.E)) :
    (A * B).map (finPart D) = A.map (finPart D) * B.map (finPart D) := Matrix.map_mul

theorem compHom_adMat_adj {D : D7} {m : ℕ} (τ : D.what₂.Tau) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (hθ : IsInfFam θ) (V : HSp D) (X : Matrix (Fin V.rank) (Fin m) D.host.E) :
    (adMat D.host.F (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram)).map (compHom θ τ) =
      (X.map (tauE D τ))ᴴ * gramAt D V τ := by
  rw [compHom_adMat τ θ hθ, Matrix.map_mul]
  congr 1
  ext i j
  exact GlobalTheory.Mem.Isom.tauE_sig D τ (X j i)

theorem exists_adelic_of_real_comps : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) {m : ℕ}
    (X : Matrix (Fin V.rank) (Fin m) D.host.E) (u : D.what₂.Tau → Matrix (Fin m) (Fin V.rank) ℂ)
    (w : D.what₂.Tau → Matrix (Fin V.rank) (Fin m) ℂ),
    (∀ τ, 1 + X.map (tauE D τ) * u τ + w τ * (X.map (tauE D τ))ᴴ * gramAt D V τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) →
    ∃ g : GA D V, (∀ τ, infMat D.sp.cm.sig V.gram (θ τ) g = 1 + X.map (tauE D τ) * u τ + w τ * (X.map (tauE D τ))ᴴ * gramAt D V τ) ∧
      ∃ (U : Matrix (Fin m) (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E))
        (W : Matrix (Fin V.rank) (Fin m) (AF D.host.F ⊗[D.host.F] D.host.E)),
        (∀ i v, (∀ τ, u τ i v = 0) → U i v = 0) ∧ (∀ v i, (∀ τ, w τ v i = 0) → W v i = 0) ∧
        (∀ i j, (∀ τ, (u τ * X.map (tauE D τ)) i j = 0) → (HMul.hMul U (GlobalTheory.SiegelSet.adMat D.host.F X) : Matrix (Fin m) (Fin m) (AF D.host.F ⊗[D.host.F] D.host.E)) i j = 0) ∧
        (matHom V g).1 = 1 + (HMul.hMul (GlobalTheory.SiegelSet.adMat D.host.F X) U : Matrix (Fin V.rank) (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) +
          (HMul.hMul W (GlobalTheory.SiegelSet.adMat D.host.F (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram)) : Matrix (Fin V.rank) (Fin V.rank) (AF D.host.F ⊗[D.host.F] D.host.E)) := by
  intro D θ hθ V m X u w hU
  obtain ⟨-, h2⟩ := GlobalTheory.SmoothForms.RealPts.glue θ hθ V
  obtain ⟨g, hg, hgτ⟩ := h2 _ hU
  obtain ⟨U, ⟨hUf, hUc⟩, -⟩ := Formalism.IndefR.Mi.realPtEx_holds (D := D) θ m V.rank hθ (fun τ i j => u τ i j)
  obtain ⟨W, ⟨hWf, hWc⟩, -⟩ := Formalism.IndefR.Mi.realPtEx_holds (D := D) θ V.rank m hθ (fun τ i j => w τ i j)
  have hUc' : ∀ τ, U.map (compHom θ τ) = u τ := hUc
  have hWc' : ∀ τ, W.map (compHom θ τ) = w τ := hWc
  have hUf' : U.map (finPart D) = 0 := hUf
  have hWf' : W.map (finPart D) = 0 := hWf
  have hzero : ∀ c : AF D.host.F ⊗[D.host.F] D.host.E, finPart D c = 0 → (∀ τ, compHom θ τ c = 0) → c = 0 :=
    fun c h1 h2 => adele_ext hθ (by rw [h1, map_zero]) fun τ => by rw [h2, map_zero]
  refine ⟨g, hgτ, U, W, fun i v h => ?_, fun v i h => ?_, fun i j h => ?_, ?_⟩
  · refine hzero _ (congrFun (congrFun hUf' i) v) fun τ => ?_
    rw [← h τ, ← hUc' τ]
    rfl
  · refine hzero _ (congrFun (congrFun hWf' v) i) fun τ => ?_
    rw [← h τ, ← hWc' τ]
    rfl
  · refine hzero _ ?_ fun τ => ?_
    · have e := map_finPart_mul U (adMat D.host.F X)
      rw [hUf', Matrix.zero_mul] at e
      exact congrFun (congrFun e i) j
    · have e := map_compHom_mul θ τ U (adMat D.host.F X)
      rw [hUc', compHom_adMat τ θ hθ] at e
      rw [← h τ, ← e]
      rfl
  · have hf : (matHom V g).1.map (finPart D) = 1 := by
      have hg' : finHom V g = 1 := hg
      have e : (finHom V g).1 = (matHom V g).1.map (finPart D) := rfl
      rw [← e, hg', Units.val_one]
    refine matrix_ext_parts hθ _ _ ?_ fun τ => ?_
    · exact hf.trans (map_one_add_of_zero (finPart D) _ _ _ _ hUf' hWf').symm
    · have e := map_one_add_of (compHom θ τ) (adMat D.host.F X) U W
        (adMat D.host.F (Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * V.gram))
        (compHom_adMat τ θ hθ X) (hUc' τ) (hWc' τ) (compHom_adMat_adj τ θ hθ V X)
      refine (hgτ τ).trans (Eq.trans ?_ e.symm)
      rw [Matrix.mul_assoc (w τ)]

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore
end
