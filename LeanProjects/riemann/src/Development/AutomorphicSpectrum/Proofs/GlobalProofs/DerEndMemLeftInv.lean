import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteDimensionalOfSlices
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockEmb
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RightTranslateCommutesCenterAction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GodementSectionSmoothBounded
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual
import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCI
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliConstantTermVanishing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockEmbNormalises
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GlRelationsDerivativePreservedStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GelfandEigenvalueCasimirScalarStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AutomorphicFunctionRestrictBlockStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BlockEmbeddingAdaptedBasisStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdaptedBasisBlockEntriesStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdaptedBasisConjugateZeroEntriesStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConjugatedMatrixUnitEntriesStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.OrthogonalSubspaceWittFrameExtensionStatement

noncomputable section

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.MonicBlock

section Res

variable {D : D7} [IsTotallyComplex D.host.E] {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {hθ : IsInfFam θ}
  {V : HSp D} {m : ℕ} {X Y : Matrix (Fin V.rank) (Fin m) D.host.E}

open GlobalTheory.CuspRep GlobalTheory.Mem.RealTranslate in

theorem resX (hW : IsWittFrame D.sp.cm.sig V.gram X Y) {l d : ℕ} (h : l + d ≤ m)
    {ι : GlobalTheory.CuspRep.GA D.host.E d →* GA D V} (hι : GlobalTheory.BlockForms.IsBlockEmb D.sp.cm.sig V.gram X Y h ι)
    {C : GL (Fin V.rank) D.host.E} (hC : GlobalTheory.BlockForms.IsAdapted D.sp.cm.sig V.gram X Y C) (τ : D.what₂.Tau)
    (F : GlobalTheory.Mem.AutSpace.SmFun θ V) (f : Sm D.host.E d) (hf : ∀ x, f.1 x = F.1 (ι x))
    (i j : Fin d) (p q : Fin V.rank) (hp : p.val = l + i.val) (hq : q.val = l + j.val) (x : GA D.host.E d) :
    (Eop (tauE D τ) i j f).1 x =
      (derEnd hθ τ (C.1.map (tauE D τ) * Matrix.single p q 1 * (C.1.map (tauE D τ))⁻¹) F).1 (ι x) := by
  have hN : 2 * m ≤ V.rank := hC.le
  have hj := j.isLt
  have hi := i.isLt
  let p' : Fin V.rank := ⟨V.rank - 1 - (l + j.val), by omega⟩
  let q' : Fin V.rank := ⟨V.rank - 1 - (l + i.val), by omega⟩
  have hp' : p'.val + l + j.val + 1 = V.rank := by simp only [p']; omega
  have hq' : q'.val + l + i.val + 1 = V.rank := by simp only [q']; omega
  have e1 := GlobalTheory.T.block_embedding_adapted_basis D θ hθ V m X Y hW l d h ι hι C hC τ F f hf i j p q p' q' hp hq hp' hq' 1 x
  have e2 := GlobalTheory.T.block_embedding_adapted_basis D θ hθ V m X Y hW l d h ι hι C hC τ F f hf i j p q p' q' hp hq hp' hq' Complex.I x
  set Ex := C.1.map (tauE D τ) * Matrix.single p q 1 * (C.1.map (tauE D τ))⁻¹
  set Ey := C.1.map (tauE D τ) * Matrix.single p' q' 1 * (C.1.map (tauE D τ))⁻¹
  have v : ∀ (a b : ℂ), (derEnd hθ τ (a • Ex - b • Ey) F).1 (ι x) =
      a * (derEnd hθ τ Ex F).1 (ι x) - b * (derEnd hθ τ Ey F).1 (ι x) := fun a b => by
    rw [map_sub, map_smul, map_smul]; rfl
  rw [v] at e1 e2
  change (1 / 2 : ℂ) * ((lieS D.host.E d i j (atEmb (tauE D τ) 1) f).1 x -
    Complex.I * (lieS D.host.E d i j (atEmb (tauE D τ) Complex.I) f).1 x) = _
  rw [e1, e2]
  simp only [map_one, Complex.conj_I]
  linear_combination ((derEnd hθ τ Ex F).1 (ι x) + (derEnd hθ τ Ey F).1 (ι x)) * (-1 / 2 : ℂ) * Complex.I_mul_I

open GlobalTheory.CuspRep GlobalTheory.Mem.RealTranslate in

theorem resY (hW : IsWittFrame D.sp.cm.sig V.gram X Y) {l d : ℕ} (h : l + d ≤ m)
    {ι : GlobalTheory.CuspRep.GA D.host.E d →* GA D V} (hι : GlobalTheory.BlockForms.IsBlockEmb D.sp.cm.sig V.gram X Y h ι)
    {C : GL (Fin V.rank) D.host.E} (hC : GlobalTheory.BlockForms.IsAdapted D.sp.cm.sig V.gram X Y C) (τ : D.what₂.Tau)
    (F : GlobalTheory.Mem.AutSpace.SmFun θ V) (f : Sm D.host.E d) (hf : ∀ x, f.1 x = F.1 (ι x))
    (i j : Fin d) (p' q' : Fin V.rank) (hp' : p'.val + l + j.val + 1 = V.rank) (hq' : q'.val + l + i.val + 1 = V.rank)
    (x : GA D.host.E d) :
    (Eop (NumberField.ComplexEmbedding.conjugate (tauE D τ)) i j f).1 x =
      (derEnd hθ τ (-(C.1.map (tauE D τ) * Matrix.single p' q' 1 * (C.1.map (tauE D τ))⁻¹)) F).1 (ι x) := by
  have hN : 2 * m ≤ V.rank := hC.le
  have hj := j.isLt
  have hi := i.isLt
  let p : Fin V.rank := ⟨l + i.val, by omega⟩
  let q : Fin V.rank := ⟨l + j.val, by omega⟩
  have e1 := GlobalTheory.T.block_embedding_adapted_basis D θ hθ V m X Y hW l d h ι hι C hC τ F f hf i j p q p' q' rfl rfl hp' hq' 1 x
  have e2 := GlobalTheory.T.block_embedding_adapted_basis D θ hθ V m X Y hW l d h ι hι C hC τ F f hf i j p q p' q' rfl rfl hp' hq' (-Complex.I) x
  set Ex := C.1.map (tauE D τ) * Matrix.single p q 1 * (C.1.map (tauE D τ))⁻¹
  set Ey := C.1.map (tauE D τ) * Matrix.single p' q' 1 * (C.1.map (tauE D τ))⁻¹
  have v : ∀ (a b : ℂ), (derEnd hθ τ (a • Ex - b • Ey) F).1 (ι x) =
      a * (derEnd hθ τ Ex F).1 (ι x) - b * (derEnd hθ τ Ey F).1 (ι x) := fun a b => by
    rw [map_sub, map_smul, map_smul]; rfl
  have v' : (derEnd hθ τ (-Ey) F).1 (ι x) = -(derEnd hθ τ Ey F).1 (ι x) := by
    rw [map_neg]; rfl
  rw [v] at e1 e2
  rw [v']
  change (1 / 2 : ℂ) * ((lieS D.host.E d i j (atEmb (NumberField.ComplexEmbedding.conjugate (tauE D τ)) 1) f).1 x -
    Complex.I * (lieS D.host.E d i j (atEmb (NumberField.ComplexEmbedding.conjugate (tauE D τ)) Complex.I) f).1 x) = _
  rw [atEmb_conj, atEmb_conj, map_one, Complex.conj_I, e1, e2]
  simp only [map_one, map_neg, Complex.conj_I, neg_neg]
  linear_combination ((derEnd hθ τ Ex F).1 (ι x) + (derEnd hθ τ Ey F).1 (ι x)) * (1 / 2 : ℂ) * Complex.I_mul_I

end Res

section Van

open GlobalTheory.Mem.RealTranslate

theorem conj_half : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 * (1 / 2) := by
  have : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.conj_ofReal, one_mul]

theorem conj_half_I : (starRingEnd ℂ) (1 / (2 * Complex.I) : ℂ) = -1 * (1 / (2 * Complex.I)) := by
  have : (1 / (2 * Complex.I) : ℂ) = ((-1 / 2 : ℝ) : ℂ) * Complex.I := by
    push_cast
    field_simp
    simp
  rw [this, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

theorem parts_mem {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (hH : Hᴴ = H) (hu : IsUnit H.det) (Z : Matrix (Fin n) (Fin n) ℂ)
    (c s : ℂ) (hs : s = 1 ∨ s = -1) (hc : starRingEnd ℂ c = s * c) :
    ((c • (Z + s • -(H⁻¹ * Zᴴ * H)))ᴴ * H + H * (c • (Z + s • -(H⁻¹ * Zᴴ * H))) = 0) := by
  have hss : star s = s := by rcases hs with rfl | rfl <;> simp
  have h2 : s * s = 1 := by rcases hs with rfl | rfl <;> simp
  have e1 : (H⁻¹ * Zᴴ * H)ᴴ * H = H * Z := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_nonsing_inv, hH]
    simp only [Matrix.mul_assoc]
    rw [nonsing_inv_mul _ hu, Matrix.mul_one]
  have e2 : H * (H⁻¹ * Zᴴ * H) = Zᴴ * H := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ hu, Matrix.one_mul]
  have hc' : star c = s * c := hc
  simp only [conjTranspose_smul, conjTranspose_add, conjTranspose_neg, Matrix.add_mul, Matrix.smul_mul, Matrix.neg_mul,
    Matrix.mul_smul, Matrix.mul_add, Matrix.mul_neg, e1, e2, hss, hc', smul_add, smul_neg, smul_smul]
  have hcs : star (c * s) = c := by
    rw [star_mul', hc', hss, mul_comm (s * c), ← mul_assoc, h2, one_mul]
  rw [hcs, mul_comm c s]
  abel

theorem isUnit_det_map {E : Type} [Field E] {n : ℕ} (C : GL (Fin n) E) (f : E →+* ℂ) : IsUnit (C.1.map f).det := by
  have : C.1.map f * f.mapMatrix (C⁻¹).1 = 1 := by
    change f.mapMatrix C.1 * _ = 1
    rw [← map_mul, Units.mul_inv, map_one]
  exact Matrix.isUnit_det_of_right_inverse this

theorem entry_parts {n : ℕ} (P Q Z W : Matrix (Fin n) (Fin n) ℂ) (c s : ℂ) (a b : Fin n) :
    (Q * (c • (Z + s • W)) * P) a b = c * ((Q * Z * P) a b + s * (Q * W * P) a b) := by
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]

variable {D : D7} [IsTotallyComplex D.host.E] {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
  {V : HSp D} {m : ℕ} {X Y : Matrix (Fin V.rank) (Fin m) D.host.E}

theorem van (hθ : IsInfFam θ) (hW : IsWittFrame D.sp.cm.sig V.gram X Y) (T : Finset (Fin m)) {l d : ℕ} (h : l + d ≤ m)
    {ι : GlobalTheory.CuspRep.GA D.host.E d →* GA D V} (hι : GlobalTheory.BlockForms.IsBlockEmb D.sp.cm.sig V.gram X Y h ι)
    (hblk : ∀ j : Fin m, l ≤ j.val → j.val + 1 < l + d → j ∉ T) (hend : ∃ k ∈ T, k.val + 1 = l + d)
    (hprev : l = 0 ∨ ∃ p ∈ T, p.val + 1 = l)
    {C : GL (Fin V.rank) D.host.E} (hC : GlobalTheory.BlockForms.IsAdapted D.sp.cm.sig V.gram X Y C) (τ : D.what₂.Tau) (p q : Fin V.rank)
    (hpq : ∃ e : ℕ, (e = l ∨ e = l + d ∨ e + l + d = V.rank ∨ e + l = V.rank) ∧ p.val < e ∧ e ≤ q.val)
    (H : GlobalTheory.Mem.AutSpace.SmFun θ V) (hH : ∀ u ∈ unip D.sp.cm.sig V.gram X T, ∀ g, H.1 (u * g) = H.1 g) (x : GlobalTheory.CuspRep.GA D.host.E d) :
    (derEnd hθ τ (C.1.map (tauE D τ) * Matrix.single p q 1 * (C.1.map (tauE D τ))⁻¹) H).1 (ι x) = 0 := by
  have hcm := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm).1
  have hJ := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND D.host.F D.host.E D.sp.cm).2 V
  have R := (GlobalTheory.T.adelicUnitary_realPoints_structure_realPlaces D).2 θ hθ V
  obtain ⟨hHer, hUn⟩ := R.1 τ
  set P := C.1.map (tauE D τ) with hP
  have hPu := isUnit_det_map C (tauE D τ)
  set Z := P * Matrix.single p q 1 * P⁻¹ with hZ
  have hZe : P⁻¹ * Z * P = Matrix.single p q 1 := by
    rw [hZ]
    calc P⁻¹ * (P * Matrix.single p q 1 * P⁻¹) * P = (P⁻¹ * P) * Matrix.single p q 1 * (P⁻¹ * P) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [nonsing_inv_mul _ hPu, Matrix.one_mul, Matrix.mul_one]
  have hnorm := (GlobalTheory.BlockForms.Norm.blockEmb_normalises _ _ D.sp.cm.sig hcm _ V.gram hJ m X Y hW T l d h ι hι hblk hend hprev).1
  have key : ∀ A ∈ lieAt V τ, (∀ a b : Fin V.rank, (P⁻¹ * A * P) a b ≠ 0 →
      ∃ e : ℕ, (e = l ∨ e = l + d ∨ e + l + d = V.rank ∨ e + l = V.rank) ∧ a.val < e ∧ e ≤ b.val) →
      Rder θ V τ A H.1 (ι x) = 0 := by
    intro A hA hs
    have hu := GlobalTheory.T.adapted_basis_block_entries D θ hθ V m X Y hW T l d h hend hprev C hC τ A hA hs
    have : (fun t : ℝ => H.1 (ι x * oneP θ V τ A t)) = fun _ => H.1 (ι x) := by
      funext t
      have e : ι x * oneP θ V τ A t = (ι x * oneP θ V τ A t * (ι x)⁻¹) * ι x := by group
      rw [e]
      exact hH _ (hnorm x _ (hu t)) _
    change deriv (fun t : ℝ => H.1 (ι x * oneP θ V τ A t)) 0 = 0
    rw [this]
    exact deriv_const _ _
  have hsupp : ∀ (c s : ℂ) (a b : Fin V.rank), (P⁻¹ * (c • (Z + s • conjAt V τ Z)) * P) a b ≠ 0 →
      ∃ e : ℕ, (e = l ∨ e = l + d ∨ e + l + d = V.rank ∨ e + l = V.rank) ∧ a.val < e ∧ e ≤ b.val := by
    intro c s a b hne
    rw [entry_parts, hZe] at hne
    by_cases h1 : (P⁻¹ * conjAt V τ Z * P) a b = 0
    · have h2 : Matrix.single p q (1 : ℂ) a b ≠ 0 := fun h0 => hne (by simp [h0, h1])
      obtain ⟨rfl, rfl⟩ : p = a ∧ q = b := by
        by_contra hc
        exact h2 (Matrix.single_apply_of_ne _ _ _ _ _ (by tauto))
      exact hpq
    · exact GlobalTheory.T.adapted_basis_conjugate_zero_entries D V m X Y hW l d h C hC τ p q a b hpq h1
  have hA : (1 / 2 : ℂ) • (Z + conjAt V τ Z) ∈ lieAt V τ := by
    have e : Z + conjAt V τ Z = Z + (1 : ℂ) • -((gramAt D V τ)⁻¹ * Zᴴ * gramAt D V τ) := by rw [one_smul]; rfl
    change ((1 / 2 : ℂ) • (Z + conjAt V τ Z))ᴴ * gramAt D V τ + gramAt D V τ * ((1 / 2 : ℂ) • (Z + conjAt V τ Z)) = 0
    rw [e]
    exact parts_mem _ hHer hUn Z (1 / 2) 1 (Or.inl rfl) conj_half
  have hB : (1 / (2 * Complex.I)) • (Z - conjAt V τ Z) ∈ lieAt V τ := by
    have e : Z - conjAt V τ Z = Z + (-1 : ℂ) • -((gramAt D V τ)⁻¹ * Zᴴ * gramAt D V τ) := by
      rw [neg_smul, one_smul, sub_eq_add_neg]; rfl
    change ((1 / (2 * Complex.I)) • (Z - conjAt V τ Z))ᴴ * gramAt D V τ + gramAt D V τ * ((1 / (2 * Complex.I)) • (Z - conjAt V τ Z)) = 0
    rw [e]
    exact parts_mem _ hHer hUn Z (1 / (2 * Complex.I)) (-1) (Or.inr rfl) conj_half_I
  have r1 := key _ hA fun a b hne => hsupp (1 / 2) 1 a b (by rwa [one_smul])
  have r2 := key _ hB fun a b hne => hsupp (1 / (2 * Complex.I)) (-1) a b (by rwa [neg_smul, one_smul, ← sub_eq_add_neg])
  change (Rder θ V τ _ H.1 + Complex.I • Rder θ V τ _ H.1) (ι x) = 0
  simp only [Pi.add_apply, Pi.smul_apply, r1, r2, smul_zero, add_zero]

end Van

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.MonicBlock

namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.MonicBlock

section Alg

variable {W Q : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup Q] [Module ℂ Q]

def pairAlg (L : W →ₗ[ℂ] Q) : Subalgebra ℂ (Module.End ℂ W × Module.End ℂ Q) where
  carrier := {p | ∀ F, L (p.1 F) = p.2 (L F)}
  mul_mem' {a b} ha hb F := by
    change L (a.1 (b.1 F)) = a.2 (b.2 (L F))
    rw [ha, hb]
  add_mem' {a b} ha hb F := by
    change L (a.1 F + b.1 F) = a.2 (L F) + b.2 (L F)
    rw [map_add, ha, hb]
  algebraMap_mem' c F := by
    change L (c • F) = c • L F
    rw [map_smul]

theorem qdet_intertwine (L : W →ₗ[ℂ] Q) {a : ℕ} (A : Fin a → Fin a → Module.End ℂ W) (B : Fin a → Fin a → Module.End ℂ Q)
    (h : ∀ i j F, L (A i j F) = B i j (L F)) (w : ℂ) (F : W) :
    L (Formalism.REAL.qdet A w F) = Formalism.REAL.qdet B w (L F) := by
  have hm := GlobalTheory.CompanionTheory.CTFin.CapStable.qdet_mem (pairAlg L) (fun i j => ((A i j, B i j) : Module.End ℂ W × Module.End ℂ Q))
    (fun i j F => h i j F) w
  have h1 : (Formalism.REAL.qdet (fun i j => ((A i j, B i j) : Module.End ℂ W × Module.End ℂ Q)) w).1 = Formalism.REAL.qdet A w :=
    GlobalTheory.CuspRep.map_qdet (AlgHom.fst ℂ (Module.End ℂ W) (Module.End ℂ Q)) (fun i j => (A i j, B i j)) w
  have h2 : (Formalism.REAL.qdet (fun i j => ((A i j, B i j) : Module.End ℂ W × Module.End ℂ Q)) w).2 = Formalism.REAL.qdet B w :=
    GlobalTheory.CuspRep.map_qdet (AlgHom.snd ℂ (Module.End ℂ W) (Module.End ℂ Q)) (fun i j => (A i j, B i j)) w
  have := hm F
  rwa [h1, h2] at this

theorem aeval_intertwine (L : W →ₗ[ℂ] Q) (a : Module.End ℂ W) (b : Module.End ℂ Q) (h : ∀ F, L (a F) = b (L F))
    (q : Polynomial ℂ) (F : W) : L (Polynomial.aeval a q F) = Polynomial.aeval b q (L F) := by
  have hm : Polynomial.aeval ((a, b) : Module.End ℂ W × Module.End ℂ Q) q ∈ pairAlg L := by
    rw [Polynomial.aeval_eq_sum_range]
    exact Subalgebra.sum_mem _ fun i _ => Subalgebra.smul_mem _ (pow_mem (show (a, b) ∈ pairAlg L from h) i) _
  have h1 : (Polynomial.aeval ((a, b) : Module.End ℂ W × Module.End ℂ Q) q).1 = Polynomial.aeval a q :=
    (Polynomial.aeval_algHom_apply (AlgHom.fst ℂ (Module.End ℂ W) (Module.End ℂ Q)) (a, b) q).symm
  have h2 : (Polynomial.aeval ((a, b) : Module.End ℂ W × Module.End ℂ Q) q).2 = Polynomial.aeval b q :=
    (Polynomial.aeval_algHom_apply (AlgHom.snd ℂ (Module.End ℂ W) (Module.End ℂ Q)) (a, b) q).symm
  have := hm F
  rwa [h1, h2] at this

def sizes (l d N : ℕ) : Fin 5 → ℕ := ![l, d, N - 2 * (l + d), d, l]

theorem sum_sizes {l d N : ℕ} (h : 2 * (l + d) ≤ N) : ∑ i, sizes l d N i = N := by
  simp [sizes, Fin.sum_univ_succ]
  omega

def starts (l d N : ℕ) : Fin 5 → ℕ := ![0, l, l + d, N - (l + d), N - l]

theorem std_val {l d N : ℕ} (hN : 2 * (l + d) ≤ N) (h : ∑ i, sizes l d N i = N) (a : Fin 5) (p : Fin (sizes l d N a)) :
    ((GlobalTheory.SmGL.stdBlocks (sizes l d N) h ⟨a, p⟩ : Fin N) : ℕ) = starts l d N a + p.val := by
  rw [GlobalTheory.SmGL.stdBlocks_val]
  congr 1
  fin_cases a <;> simp [Fin.sum_univ_succ, sizes, starts] <;> omega

theorem cut_of_blk {l d N : ℕ} (hN : 2 * (l + d) ≤ N) (h : ∑ i, sizes l d N i = N) (p q : Fin N)
    (hpq : GlobalTheory.SmGL.blk (GlobalTheory.SmGL.stdBlocks (sizes l d N) h) p < GlobalTheory.SmGL.blk (GlobalTheory.SmGL.stdBlocks (sizes l d N) h) q) :
    ∃ e : ℕ, (e = l ∨ e = l + d ∨ e + l + d = N ∨ e + l = N) ∧ p.val < e ∧ e ≤ q.val := by
  obtain ⟨⟨a, i⟩, rfl⟩ := (GlobalTheory.SmGL.stdBlocks (sizes l d N) h).surjective p
  obtain ⟨⟨b, j⟩, rfl⟩ := (GlobalTheory.SmGL.stdBlocks (sizes l d N) h).surjective q
  have hab : a < b := by simpa [GlobalTheory.SmGL.blk] using hpq
  have hi := i.isLt
  have key : ∀ a b : Fin 5, a < b → starts l d N a + sizes l d N a ≤ starts l d N b ∧
      (starts l d N b = l ∨ starts l d N b = l + d ∨ starts l d N b + l + d = N ∨ starts l d N b + l = N) := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp [starts, sizes] at hab ⊢ <;> omega
  obtain ⟨k1, k2⟩ := key a b hab
  refine ⟨starts l d N b, k2, ?_, ?_⟩
  · rw [std_val hN]; omega
  · rw [std_val hN]; omega

end Alg

section Core

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

def leftInv (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (U : Subgroup (GA D V)) : Submodule ℂ (GlobalTheory.Mem.AutSpace.SmFun θ V) where
  carrier := {F | ∀ u ∈ U, ∀ g, F.1 (u * g) = F.1 g}
  add_mem' {a b} ha hb u hu g := by
    change a.1 (u * g) + b.1 (u * g) = a.1 g + b.1 g
    rw [ha u hu, hb u hu]
  zero_mem' _ _ _ := rfl
  smul_mem' c a ha u hu g := by
    change c • a.1 (u * g) = c • a.1 g
    rw [ha u hu]

theorem derEnd_mem_leftInv (hθ : IsInfFam θ) (U : Subgroup (GA D V)) (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (F : GlobalTheory.Mem.AutSpace.SmFun θ V) (hF : F ∈ leftInv θ U) : GlobalTheory.Mem.RealTranslate.derEnd hθ τ Z F ∈ leftInv θ U := by
  intro u hu g
  change RderC θ V τ Z F.1 (u * g) = RderC θ V τ Z F.1 g
  simp only [RderC, Rder, Pi.add_apply, Pi.smul_apply, mul_assoc, hF u hu]

open GlobalTheory.CuspRep in

theorem core [IsTotallyComplex D.host.E] (hθ : IsInfFam θ) {m : ℕ} {X : Matrix (Fin V.rank) (Fin m) D.host.E} (T : Finset (Fin m))
    {l d : ℕ} (ι : GlobalTheory.CuspRep.GA D.host.E d →* GA D V) (hN : 2 * (l + d) ≤ V.rank)
    (hsm : ∀ F : GlobalTheory.Mem.AutSpace.SmFun θ V, (fun x => F.1 (ι x)) ∈ Sm D.host.E d)
    (τ' : D.what₂.Tau) (τ : D.host.E →+* ℂ) (ck : ℕ → ℂ)
    (M : Fin V.rank → Fin V.rank → Matrix (Fin V.rank) (Fin V.rank) ℂ) (hM : Formalism.REAL.GlRel M)
    (hsp : Submodule.span ℂ (Set.range fun p : Fin V.rank × Fin V.rank => M p.1 p.2) = ⊤)
    (hvan : ∀ p q : Fin V.rank, (∃ e : ℕ, (e = l ∨ e = l + d ∨ e + l + d = V.rank ∨ e + l = V.rank) ∧ p.val < e ∧ e ≤ q.val) →
      ∀ H : GlobalTheory.Mem.AutSpace.SmFun θ V, (∀ u ∈ unip D.sp.cm.sig V.gram X T, ∀ g, H.1 (u * g) = H.1 g) → ∀ x,
        (GlobalTheory.Mem.RealTranslate.derEnd hθ τ' (M p q) H).1 (ι x) = 0)
    (hres : ∀ (F : GlobalTheory.Mem.AutSpace.SmFun θ V) (f : Sm D.host.E d), (∀ x, f.1 x = F.1 (ι x)) →
      ∀ (i j : Fin d) (p q : Fin V.rank), p.val = l + i.val → q.val = l + j.val → ∀ x,
        (Eop τ i j f).1 x = (GlobalTheory.Mem.RealTranslate.derEnd hθ τ' (M p q) F).1 (ι x)) (u : ℂ) :
    ∃ q : Polynomial ℂ, q.Monic ∧
      ∀ ψ : GlobalTheory.Mem.AutSpace.SmFun θ V, (∀ u ∈ unip D.sp.cm.sig V.gram X T, ∀ g, ψ.1 (u * g) = ψ.1 g) →
        (∀ k, gelf θ V τ' k ψ.1 = ck k • ψ.1) → ∀ f : Sm D.host.E d, (∀ x, f.1 x = ψ.1 (ι x)) →
          Polynomial.aeval (cap (a := d) τ u) q f = 0 := by
  classical
  have hS := sum_sizes hN
  let Xf : Fin V.rank → Fin V.rank → Module.End ℂ (GlobalTheory.Mem.AutSpace.SmFun θ V) :=
    fun p q => GlobalTheory.Mem.RealTranslate.derEnd hθ τ' (M p q)
  let L : GlobalTheory.Mem.AutSpace.SmFun θ V →ₗ[ℂ] Sm D.host.E d :=
    { toFun := fun F => ⟨fun x => F.1 (ι x), hsm F⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let U : Subgroup (GA D V) := unip D.sp.cm.sig V.gram X T
  let W₀ : Set (GlobalTheory.Mem.AutSpace.SmFun θ V) := {F | F ∈ leftInv θ U ∧ ∀ k, gelf θ V τ' k F.1 = ck k • F.1}
  obtain ⟨q, hq, hq0⟩ := GlobalTheory.T.gl_relations_triangular_annihilation _ _ 5 V.rank (sizes l d V.rank) hS Xf (GlobalTheory.T.gl_relations_derivative_preserved D θ hθ V τ' M hM) (leftInv θ U)
    (fun p q F hF => derEnd_mem_leftInv hθ U τ' _ F hF) L
    (fun p q hpq F hF => Subtype.ext (funext fun x => hvan p q (cut_of_blk hN hS p q hpq) F hF x)) W₀ (fun F hF => hF.1)
    (fun v => by
      obtain ⟨s, hs⟩ := GlobalTheory.T.gelfand_eigenvalue_casimir_scalar D θ hθ V τ' M hM hsp ck v
      exact ⟨s, fun F hF => hs F hF.2⟩) 1 (u + ((d : ℂ) - 1) / 2)
  refine ⟨q, hq, fun ψ hψ hg f hf => ?_⟩
  have e0 : f = L ψ := Subtype.ext (funext hf)
  have hB : ∀ (i j : Fin d) (F : GlobalTheory.Mem.AutSpace.SmFun θ V),
      L (Xf (GlobalTheory.SmGL.stdBlocks (sizes l d V.rank) hS ⟨1, i⟩) (GlobalTheory.SmGL.stdBlocks (sizes l d V.rank) hS ⟨1, j⟩) F) =
        Eop τ i j (L F) := fun i j F => Subtype.ext (funext fun x =>
    (hres F (L F) (fun _ => rfl) i j _ _ (std_val hN hS 1 i) (std_val hN hS 1 j) x).symm)
  have h1 := aeval_intertwine L _ (cap (a := d) τ u) (fun F => qdet_intertwine L _ (Eop τ) hB (u + ((d : ℂ) - 1) / 2) F) q ψ
  rw [e0, ← h1]
  exact hq0 ψ ⟨hψ, hg⟩

end Core

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.MonicBlock

namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.MonicBlock

section Units

variable {n : ℕ}

theorem glRel_conj (P Q : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1) :
    Formalism.REAL.GlRel (fun p q => P * Matrix.single p q (1 : ℂ) * Q) := by
  have e : ∀ A B : Matrix (Fin n) (Fin n) ℂ, (P * A * Q) * (P * B * Q) = P * (A * B) * Q := fun A B => by
    calc (P * A * Q) * (P * B * Q) = P * A * (Q * P) * B * Q := by simp only [Matrix.mul_assoc]
      _ = P * (A * B) * Q := by rw [hQP]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  intro a b c d
  simp only [e]
  rw [← Matrix.sub_mul, ← Matrix.mul_sub]
  have s1 : Matrix.single a b (1 : ℂ) * Matrix.single c d 1 = if b = c then Matrix.single a d 1 else 0 := by
    split_ifs with h
    · subst h; simp
    · exact Matrix.single_mul_single_of_ne _ _ _ _ h _
  have s2 : Matrix.single c d (1 : ℂ) * Matrix.single a b 1 = if d = a then Matrix.single c b 1 else 0 := by
    split_ifs with h
    · subst h; simp
    · exact Matrix.single_mul_single_of_ne _ _ _ _ h _
  rw [s1, s2]
  split_ifs <;> simp [Matrix.sub_mul, Matrix.mul_sub]

theorem glRel_conj_rev (P Q : Matrix (Fin n) (Fin n) ℂ) (hQP : Q * P = 1) :
    Formalism.REAL.GlRel (fun p q : Fin n => -(P * Matrix.single q.rev p.rev (1 : ℂ) * Q)) := by
  have h := glRel_conj P Q hQP
  intro a b c d
  have h1 := h d.rev c.rev b.rev a.rev
  simp only [Fin.rev_inj] at h1
  simp only [neg_mul_neg]
  rw [← neg_sub, h1]
  simp only [eq_comm (a := c) (b := b), eq_comm (a := a) (b := d)]
  split_ifs <;> simp
  abel

theorem span_conj (P Q : Matrix (Fin n) (Fin n) ℂ) (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    Submodule.span ℂ (Set.range fun p : Fin n × Fin n => P * Matrix.single p.1 p.2 (1 : ℂ) * Q) = ⊤ := by
  rw [eq_top_iff]
  intro Z _
  have e : Z = ∑ a, ∑ b, (Q * Z * P) a b • (P * Matrix.single a b (1 : ℂ) * Q) := by
    have h1 : Q * Z * P = ∑ a, ∑ b, (Q * Z * P) a b • Matrix.single a b (1 : ℂ) := by
      simpa [Matrix.smul_single] using Matrix.matrix_eq_sum_single (Q * Z * P)
    calc Z = P * (Q * Z * P) * Q := by
          simp only [← Matrix.mul_assoc]; rw [hPQ, Matrix.one_mul, Matrix.mul_assoc, hPQ, Matrix.mul_one]
      _ = _ := by
          conv_lhs => rw [h1]
          simp only [Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [e]
  exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨(a, b), rfl⟩)

theorem span_conj_rev (P Q : Matrix (Fin n) (Fin n) ℂ) (hPQ : P * Q = 1) (hQP : Q * P = 1) :
    Submodule.span ℂ (Set.range fun p : Fin n × Fin n => -(P * Matrix.single p.2.rev p.1.rev (1 : ℂ) * Q)) = ⊤ := by
  rw [eq_top_iff, ← span_conj P Q hPQ hQP]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨⟨a, b⟩, rfl⟩
  have := (Submodule.span ℂ (Set.range fun p : Fin n × Fin n => -(P * Matrix.single p.2.rev p.1.rev (1 : ℂ) * Q))).neg_mem
    (Submodule.subset_span ⟨(b.rev, a.rev), rfl⟩)
  simpa using this

end Units

open GlobalTheory.CuspRep in

theorem monic_block : ∀ (D : D7) [IsTotallyComplex D.host.E] (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ →
    ∀ (V : HSp D) (c : D.what₂.Tau → ℕ → ℂ) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E),
    IsWittFrame D.sp.cm.sig V.gram X Y → ∀ (T : Finset (Fin m)) (l d : ℕ) (h : l + d ≤ m)
    (ι : GlobalTheory.CuspRep.GA D.host.E d →* GA D V), GlobalTheory.BlockForms.IsBlockEmb D.sp.cm.sig V.gram X Y h ι → 1 ≤ d →
    (∀ j : Fin m, l ≤ j.val → j.val + 1 < l + d → j ∉ T) → (∃ k ∈ T, k.val + 1 = l + d) →
    (l = 0 ∨ ∃ p ∈ T, p.val + 1 = l) →
    ∀ (τ : D.host.E →+* ℂ) (u : ℂ), ∃ q : Polynomial ℂ, q.Monic ∧
      ∀ φ : GA D V → ℂ, IsSmModOn D.sp.cm.sig V.gram (leftSub V X Y T : Set (GA D V)) φ →
        (∀ τ' k, gelf θ V τ' k φ = c τ' k • φ) → ∀ (g₀ : GA D V) (f : GlobalTheory.CuspRep.Sm D.host.E d),
          (∀ x, f.1 x = φ (ι x * g₀)) → Polynomial.aeval (GlobalTheory.CuspRep.cap (a := d) τ u) q f = 0 := by
  intro D _ θ hθ V c m X Y hW T l d h ι hι hd hblk hend hprev τ u
  classical
  obtain ⟨C, hC⟩ := GlobalTheory.T.exists_adapted_witt_basis D V m X Y hW
  have hN : 2 * (l + d) ≤ V.rank := by have := hC.le; omega
  have hsm := GlobalTheory.T.automorphic_function_restrict_block D θ hθ V m X Y hW l d h ι hι
  obtain ⟨τ', hτ'⟩ := Formalism.L2.Fam.ThC.tauE_or (D := D) τ
  set P : Matrix (Fin V.rank) (Fin V.rank) ℂ := C.1.map (tauE D τ') with hP
  set Q : Matrix (Fin V.rank) (Fin V.rank) ℂ := P⁻¹ with hQ
  have hu : IsUnit P.det := by
    have : P * (tauE D τ').mapMatrix (C⁻¹).1 = 1 := by
      change (tauE D τ').mapMatrix C.1 * _ = 1
      rw [← map_mul, Units.mul_inv, map_one]
    exact Matrix.isUnit_det_of_right_inverse this
  have hPQ : P * Q = 1 := Matrix.mul_nonsing_inv _ hu
  have hQP : Q * P = 1 := Matrix.nonsing_inv_mul _ hu
  have key : ∃ q : Polynomial ℂ, q.Monic ∧
      ∀ ψ : GlobalTheory.Mem.AutSpace.SmFun θ V, (∀ u ∈ unip D.sp.cm.sig V.gram X T, ∀ g, ψ.1 (u * g) = ψ.1 g) →
        (∀ k, gelf θ V τ' k ψ.1 = c τ' k • ψ.1) → ∀ f : Sm D.host.E d, (∀ x, f.1 x = ψ.1 (ι x)) →
          Polynomial.aeval (cap (a := d) τ u) q f = 0 := by
    rcases hτ' with e | e
    · subst e
      exact core hθ T ι hN hsm τ' _ (c τ') (fun p q => P * Matrix.single p q 1 * Q) (glRel_conj P Q hQP) (span_conj P Q hPQ hQP)
        (fun p q hpq H hH x => van hθ hW T h hι hblk hend hprev hC τ' p q hpq H hH x)
        (fun F f hf i j p q hp hq x => resX hW h hι hC τ' F f hf i j p q hp hq x) u
    · have e' : τ = NumberField.ComplexEmbedding.conjugate (tauE D τ') := by
        rw [e]
        ext x
        simp [NumberField.ComplexEmbedding.conjugate_coe_eq]
      subst e'
      refine core hθ T ι hN hsm τ' _ (c τ') (fun p q => -(P * Matrix.single q.rev p.rev 1 * Q)) (glRel_conj_rev P Q hQP)
        (span_conj_rev P Q hPQ hQP) (fun p q hpq H hH x => ?_)
        (fun F f hf i j p q hp hq x => resY hW h hι hC τ' F f hf i j q.rev p.rev ?_ ?_ x) u
      · obtain ⟨e₀, he, h1, h2⟩ := hpq
        have hv := van hθ hW T h hι hblk hend hprev hC τ' q.rev p.rev
          ⟨V.rank - e₀, ?_, ?_, ?_⟩ H hH x
        · rw [map_neg]
          change -((GlobalTheory.Mem.RealTranslate.derEnd hθ τ' _ H).1 (ι x)) = 0
          rw [hv, neg_zero]
        · have := q.isLt
          rcases he with he | he | he | he <;> omega
        · have := q.isLt
          simp only [Fin.val_rev]; omega
        · have := p.isLt
          simp only [Fin.val_rev]; omega
      · have := q.isLt
        simp only [Fin.val_rev]; omega
      · have := p.isLt
        simp only [Fin.val_rev]; omega
  obtain ⟨q, hq, hq0⟩ := key
  refine ⟨q, hq, fun φ hφ hg g₀ f hf => ?_⟩
  have hs : φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V := GlobalTheory.SphSmooth.mem_smFun_of_isSm hθ hφ.smooth
  let ψ : GlobalTheory.Mem.AutSpace.SmFun θ V := ⟨rTr V g₀ φ, GlobalTheory.RegSch.CentreRight.rTr_mem_all hθ g₀ hs⟩
  refine hq0 ψ (fun v hv g => ?_) (fun k => ?_) f hf
  · change φ (v * g * g₀) = φ (g * g₀)
    rw [mul_assoc]
    exact hφ.left v (Subgroup.mem_sup_left hv) _
  · change gelf θ V τ' k (rTr V g₀ φ) = c τ' k • rTr V g₀ φ
    rw [GlobalTheory.RegSch.CentreRight.gelf_rTr_all hθ g₀ τ' k hs, hg]
    rfl

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.MonicBlock

end
