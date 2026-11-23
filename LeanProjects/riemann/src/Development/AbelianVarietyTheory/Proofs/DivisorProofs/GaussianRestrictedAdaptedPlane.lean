import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordinatesInsertZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFockVacuumLineUniqueOfHeisenbergDerivatiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanEigenOrthonormalFrameExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockToSchrodingerMapExistsOfArchHeisenbergDerivaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneLeftInverseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneCartanInvolutionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneSignatureDropStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.PlaneEv

noncomputable section
namespace GlobalTheory.ThK.PlaneEv

theorem jm_transpose (P Q : ℕ) : (Formalism.BasicNotions.TH.Jm P Q)ᵀ = Formalism.BasicNotions.TH.Jm P Q := by
  simp [Formalism.BasicNotions.TH.Jm, Formalism.UG.Jpq, Matrix.fromBlocks_transpose]

theorem rho_zero {R : Type} [CommRing R] [Invertible (2 : R)] {V : Type} [AddCommGroup V] [Module R V] {Bf : V → V → R}
    {κ : Type} [Fintype κ] (co : Darboux Bf κ) (ψ : AddChar R ℂ) (w : V) : co.rho ψ w 0 = 0 := by
  funext x; simp [Darboux.rho, schr]

theorem leftInv_at {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E} {d d₁ r' s' i₀ i₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁}
    (hW : W.IsSkew σ B r' s') (hH : H'.IsAdapted σ B W W₁ i₀ i₁) (w : InfinitePlace F) :
    ∃ L : Matrix (Fin d₁) (Fin d) ℂ, L * H'.ι.map (B.emb w).1 = 1 := by
  obtain ⟨L, hL⟩ := GlobalTheory.T.adapted_plane_left_inverse F E σ B d d₁ r' s' i₀ i₁ W W₁ H' hW hH
  refine ⟨L.map (B.emb w).1, ?_⟩
  rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero _) (map_one _)]

theorem cartan_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E} {d d₁ r' s' i₀ i₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁}
    (hB : B.IsGood σ) (hW : W.IsSkew σ B r' s') (hH : H'.IsAdapted σ B W W₁ i₀ i₁) (w : InfinitePlace F) :
    IsCartan (Complex.I • W₁.J.map (B.emb w).1) (W₁.θ w) :=
  GlobalTheory.T.adapted_plane_cartan_involution F E σ B d d₁ r' s' i₀ i₁ W W₁ H' hB hW hH w (leftInv_at hW hH w)

theorem sig_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E} {d d₁ r' s' i₀ i₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁}
    (hB : B.IsGood σ) (hW : W.IsSkew σ B r' s') (hH : H'.IsAdapted σ B W W₁ i₀ i₁) (w : InfinitePlace F) :
    HasSig (Complex.I • W₁.J.map (B.emb w).1) (r' - 1) (s' - 1) :=
  GlobalTheory.T.adapted_plane_signature_drop F E σ B d d₁ r' s' i₀ i₁ W W₁ H' hB hW hH w (leftInv_at hW hH w)

theorem vac_line_of_model : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d d₁ r s r' s' i₀ i₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (M₁ : Model σ X W₁),
    B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → H'.IsAdapted σ B W W₁ i₀ i₁ → GlobalTheory.RealLift.DerEx →
    GlobalTheory.RealLift.ActsLaws → ∃ g : SInf F (Fin n × Fin d₁), ∀ g₀, M₁.IsGauss B.ψ B.emb g₀ → ∃ z : ℂ, g₀ = z • g := by
  intro F E _ _ _ _ _ σ B n d d₁ r s r' s' i₀ i₁ X W W₁ H' M₁ hB hX hW hH hDer hLaws
  choose A hA hAθ using fun w => GlobalTheory.T.cartanEigen_orthonormalFrame_exists n r s (X.J.map (B.emb w).1) (X.θ w) (hX.sig w) (hX.cartan w)
  choose C hC hCθ using fun w => GlobalTheory.T.cartanEigen_orthonormalFrame_exists d₁ (r' - 1) (s' - 1) (Complex.I • W₁.J.map (B.emb w).1) (W₁.θ w)
    (sig_one hB hW hH w) (cartan_one hB hW hH w)
  have hFr : GlobalTheory.RealLift.Framed B.emb (incM F X.J) (incM F W₁.J) 1 Complex.I A C :=
    ⟨one_mul _, fun w => by rw [incM_map_piInf_emb, one_smul]; exact hA w,
      fun w => by rw [incM_map_piInf_emb]; exact hC w⟩
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.fockToSchrodingerMapExists_of_archHeisenbergDerivatives hDer F E σ (Fin n) (Fin d₁) (Fin n × Fin d₁) r s (r' - 1) (s' - 1) B.ψ B.emb _ _ M₁.co
    1 Complex.I A C hB.cm hB.std hFr
  refine ⟨Φ (PiTensorProduct.tprod ℂ fun _ => 1), fun g₀ hg₀ => ?_⟩
  obtain ⟨ε, hε⟩ := hg₀
  refine GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives hDer F E σ (Fin n) (Fin d₁) (Fin n × Fin d₁) r s (r' - 1) (s' - 1) B.ψ B.emb _ _ M₁.co 1 Complex.I
    A C Φ hB.cm hB.std hFr hΦ g₀ ε ?_
  intro u u' hu hu' c hc hc' f f' hf hf'
  have hz : ∀ v, M₁.co.rho B.ψ v 0 = 0 := rho_zero M₁.co B.ψ
  refine hε u u' hu hu' ?_ f f' ((hLaws F (Fin n × Fin d₁) g₀ f f).1 _ (fun t => hz _) hf)
    ((hLaws F (Fin n × Fin d₁) g₀ f' f').1 _ (fun t => hz _) hf')
  intro w
  rw [hc' w, hc w]
  have h1 : Matrix.transpose (C w) * (W₁.θ w)ᵀ = Formalism.BasicNotions.TH.Jm (r' - 1) (s' - 1) * (C w)ᵀ := by
    rw [← Matrix.transpose_mul, hCθ w, Matrix.transpose_mul, jm_transpose]
  rw [Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  calc A w * (Formalism.BasicNotions.TH.Jm r s * c w * Formalism.BasicNotions.TH.Jm (r' - 1) (s' - 1)) * (C w)ᵀ
      = (X.θ w * A w) * c w * (Formalism.BasicNotions.TH.Jm (r' - 1) (s' - 1) * (C w)ᵀ) := by
        rw [hAθ w]; simp only [Matrix.mul_assoc]
    _ = X.θ w * (A w * c w * (C w)ᵀ) * (W₁.θ w)ᵀ := by
        rw [← h1]; simp only [Matrix.mul_assoc]

end GlobalTheory.ThK.PlaneEv
