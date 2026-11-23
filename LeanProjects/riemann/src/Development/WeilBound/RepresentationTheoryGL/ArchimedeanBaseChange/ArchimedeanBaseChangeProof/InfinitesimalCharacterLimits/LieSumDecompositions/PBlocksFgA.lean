import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksDefs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CapelliDetDiagonalBlockActsByInfinitesimalCharac
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LieDSingleLeviEmbEqZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CapelliLeviFactorizationSum
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSliceTens

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs GlobalTheory.SmGL

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockFiniteGeneration

set_option linter.unusedSectionVars false

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r s : ℕ}

theorem h2 (r s : ℕ) : ∑ i, (![r, s] : Fin 2 → ℕ) i = r + s := CapFactor.two_sum _

def sl0 (m₂ : GA E s) : Sm E (r + s) →ₗ[ℂ] Sm E r :=
  GlobalTheory.BlockCap.restrLin (stdBlocks ![r, s] (h2 r s)) (CapFactor.levPair (1, m₂)) 0

def sl1 (m₁ : GA E r) : Sm E (r + s) →ₗ[ℂ] Sm E s :=
  GlobalTheory.BlockCap.restrLin (stdBlocks ![r, s] (h2 r s)) (CapFactor.levPair (m₁, 1)) 1

theorem update0 (m₁ : GA E r) (m₂ : GA E s) :
    Function.update (CapFactor.levPair (n := ![r, s]) (1, m₂)) 0 m₁ = CapFactor.levPair (m₁, m₂) := by
  funext i
  fin_cases i <;> rfl

theorem update1 (m₁ : GA E r) (m₂ : GA E s) :
    Function.update (CapFactor.levPair (n := ![r, s]) (m₁, 1)) 1 m₂ = CapFactor.levPair (m₁, m₂) := by
  funext i
  fin_cases i <;> rfl

theorem left_slice_apply (m₂ : GA E s) (F : Sm E (r + s)) (m₁ : GA E r) :
    (sl0 m₂ F).1 m₁ = F.1 (lev (Ad E) r s (m₁, m₂)) := by
  show F.1 (leviEmb (Ad E) (stdBlocks ![r, s] (h2 r s))
    (Function.update (CapFactor.levPair (n := ![r, s]) (1, m₂)) 0 m₁)) = _
  rw [update0]
  exact congrArg F.1 (CapFactor.lev_eq_leviEmb (R := Ad E) ![r, s] (h2 r s) (m₁, m₂)).symm

theorem right_slice_apply (m₁ : GA E r) (F : Sm E (r + s)) (m₂ : GA E s) :
    (sl1 m₁ F).1 m₂ = F.1 (lev (Ad E) r s (m₁, m₂)) := by
  show F.1 (leviEmb (Ad E) (stdBlocks ![r, s] (h2 r s))
    (Function.update (CapFactor.levPair (n := ![r, s]) (m₁, 1)) 1 m₂)) = _
  rw [update1]
  exact congrArg F.1 (CapFactor.lev_eq_leviEmb (R := Ad E) ![r, s] (h2 r s) (m₁, m₂)).symm

example {a : ℕ} (A B : Matrix (Fin a) (Fin a) (Cinf E)) : toL (A + B) = toL A + toL B := rfl

theorem yp_one {a : ℕ} : BlockDerivatives.yp (1 : Kinf E a) (1 : GL (Fin a) (Af E)) = 1 := by
  simp [BlockDerivatives.yp]

abbrev e2 (r s : ℕ) := stdBlocks ![r, s] (h2 r s)

theorem left_slice_lie_first_block (m₂ : GA E s) (Y : Lie E r) (F : Sm E (r + s)) :
    sl0 m₂ (lie E (r + s) (GlobalTheory.BlockCap.blockCLM (e2 r s) 0 Y) F) = lie E r Y (sl0 m₂ F) :=
  LinearMap.congr_fun (GlobalTheory.BlockCap.restrLin_lie (e2 r s) (CapFactor.levPair (1, m₂)) 0 Y) F

theorem right_slice_lie_second_block (m₁ : GA E r) (Y : Lie E s) (F : Sm E (r + s)) :
    sl1 m₁ (lie E (r + s) (GlobalTheory.BlockCap.blockCLM (e2 r s) 1 Y) F) = lie E s Y (sl1 m₁ F) :=
  LinearMap.congr_fun (GlobalTheory.BlockCap.restrLin_lie (e2 r s) (CapFactor.levPair (m₁, 1)) 1 Y) F

theorem std0 (p : Fin r) : (e2 r s) ⟨0, p⟩ = Fin.castAdd s p := CapFactor.std_zero ![r, s] (h2 r s) p

theorem std1 (q : Fin s) : (e2 r s) ⟨1, q⟩ = Fin.natAdd r q := CapFactor.std_one ![r, s] (h2 r s) q

theorem lev_eq (m : GA E r × GA E s) : lev (Ad E) r s m = leviEmb (Ad E) (e2 r s) (CapFactor.levPair m) :=
  CapFactor.lev_eq_leviEmb ![r, s] (h2 r s) m

theorem toL_single_cc (p q : Fin r) (x : Cinf E) :
    (toL (Matrix.single (Fin.castAdd s p) (Fin.castAdd s q) x) : Lie E (r + s)) =
      GlobalTheory.BlockCap.blockCLM (e2 r s) 0 (toL (Matrix.single p q x)) := by
  have h := GlobalTheory.BlockCap.blockLin_single (E := E) (e2 r s) 0 p q x
  rw [std0, std0] at h
  exact h.symm

theorem toL_single_nn (p q : Fin s) (x : Cinf E) :
    (toL (Matrix.single (Fin.natAdd r p) (Fin.natAdd r q) x) : Lie E (r + s)) =
      GlobalTheory.BlockCap.blockCLM (e2 r s) 1 (toL (Matrix.single p q x)) := by
  have h := GlobalTheory.BlockCap.blockLin_single (E := E) (e2 r s) 1 p q x
  rw [std1, std1] at h
  exact h.symm

theorem unipRad_inv (F : Sm E (r + s)) (hF : ∀ (x : BlockIx (r + s) r → Ad E) g, F.1 (unip x * g) = F.1 g) :
    ∀ u ∈ unipRad (Ad E) (e2 r s), ∀ g, F.1 (u * g) = F.1 g := fun u hu g => by
  obtain ⟨x, rfl⟩ := CapFactor.exists_unip_of_mem ![r, s] (h2 r s) hu
  exact hF x g

theorem lie_upper_lev (F : Sm E (r + s)) (hF : ∀ (x : BlockIx (r + s) r → Ad E) g, F.1 (unip x * g) = F.1 g)
    (p : Fin r) (q : Fin s) (x : Cinf E) (m : GA E r × GA E s) :
    (lie E (r + s) (toL (Matrix.single (Fin.castAdd s p) (Fin.natAdd r q) x)) F).1 (lev (Ad E) r s m) = 0 := by
  have hpq : blk (e2 r s) (Fin.castAdd s p) < blk (e2 r s) (Fin.natAdd r q) := by
    have b0 : blk (e2 r s) ((e2 r s) ⟨0, p⟩) = 0 := blk_apply (e2 r s) 0 p
    have b1 : blk (e2 r s) ((e2 r s) ⟨1, q⟩) = 1 := blk_apply (e2 r s) 1 q
    rw [std0] at b0
    rw [std1] at b1
    rw [b0, b1]
    decide
  have := GlobalTheory.UnipZero.lieD_single_leviEmb_eq_zero E ![r, s] (e2 r s) F (unipRad_inv F hF) _ _ hpq x
    (CapFactor.levPair m)
  rw [lev_eq]
  exact this

theorem lie_sum_single (X : Lie E (r + s)) (F : Sm E (r + s)) :
    lie E (r + s) X F = ∑ p, ∑ q, lie E (r + s) (toL (Matrix.single p q (X p q))) F := by
  have hdec : X = ∑ p, ∑ q, (toL (Matrix.single p q (X p q)) : Lie E (r + s)) :=
    Matrix.matrix_eq_sum_single (Matrix.of X)
  conv_lhs => rw [hdec]
  rw [map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_sum, LinearMap.sum_apply]

theorem right_slice_eq_sum (F : Sm E (r + s)) {n : ℕ} (b : Fin n → Sm E r) (q : Fin n → Sm E s)
    (hexp : ∀ m : GA E r × GA E s, F.1 (lev (Ad E) r s m) = ∑ i, (b i).1 m.1 * (q i).1 m.2) (m₁ : GA E r) :
    sl1 m₁ F = ∑ i, (b i).1 m₁ • q i := by
  refine Subtype.ext (funext fun m₂ => ?_)
  rw [right_slice_apply, hexp (m₁, m₂), Submodule.coe_sum, Finset.sum_apply]
  rfl

theorem left_slice_eq_sum (F : Sm E (r + s)) {n : ℕ} (b : Fin n → Sm E r) (q : Fin n → Sm E s)
    (hexp : ∀ m : GA E r × GA E s, F.1 (lev (Ad E) r s m) = ∑ i, (b i).1 m.1 * (q i).1 m.2) (m₂ : GA E s) :
    sl0 m₂ F = ∑ i, (q i).1 m₂ • b i := by
  refine Subtype.ext (funext fun m₁ => ?_)
  rw [left_slice_apply, hexp (m₁, m₂), Submodule.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  change _ = (q i).1 m₂ * (b i).1 m₁
  ring

theorem left_slice_lie_second_block (F : Sm E (r + s)) {n : ℕ} (b : Fin n → Sm E r) (q : Fin n → Sm E s)
    (hexp : ∀ m : GA E r × GA E s, F.1 (lev (Ad E) r s m) = ∑ i, (b i).1 m.1 * (q i).1 m.2) (Y : Lie E s)
    (m₂ : GA E s) :
    sl0 m₂ (lie E (r + s) (GlobalTheory.BlockCap.blockCLM (e2 r s) 1 Y) F) = ∑ i, (lie E s Y (q i)).1 m₂ • b i := by
  refine Subtype.ext (funext fun m₁ => ?_)
  rw [left_slice_apply, ← right_slice_apply, right_slice_lie_second_block, right_slice_eq_sum F b q hexp, map_sum, Submodule.coe_sum, Finset.sum_apply,
    Submodule.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]
  change (b i).1 m₁ * (lie E s Y (q i)).1 m₂ = (lie E s Y (q i)).1 m₂ * (b i).1 m₁
  ring

theorem right_slice_lie_first_block (F : Sm E (r + s)) {n : ℕ} (b : Fin n → Sm E r) (q : Fin n → Sm E s)
    (hexp : ∀ m : GA E r × GA E s, F.1 (lev (Ad E) r s m) = ∑ i, (b i).1 m.1 * (q i).1 m.2) (Y : Lie E r)
    (m₁ : GA E r) :
    sl1 m₁ (lie E (r + s) (GlobalTheory.BlockCap.blockCLM (e2 r s) 0 Y) F) = ∑ i, (lie E r Y (b i)).1 m₁ • q i := by
  refine Subtype.ext (funext fun m₂ => ?_)
  rw [right_slice_apply, ← left_slice_apply, left_slice_lie_first_block, left_slice_eq_sum F b q hexp, map_sum, Submodule.coe_sum, Finset.sum_apply,
    Submodule.coe_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul]
  change (q i).1 m₂ * (lie E r Y (b i)).1 m₁ = (lie E r Y (b i)).1 m₁ * (q i).1 m₂
  ring

theorem left_slice_single_first (m₂ : GA E s) (p q : Fin r) (x : Cinf E) (F : Sm E (r + s)) :
    sl0 m₂ (lie E (r + s) (toL (Matrix.single (Fin.castAdd s p) (Fin.castAdd s q) x)) F) =
      lie E r (toL (Matrix.single p q x)) (sl0 m₂ F) := by
  rw [toL_single_cc]
  exact left_slice_lie_first_block m₂ _ F

theorem right_slice_single_second (m₁ : GA E r) (p q : Fin s) (x : Cinf E) (F : Sm E (r + s)) :
    sl1 m₁ (lie E (r + s) (toL (Matrix.single (Fin.natAdd r p) (Fin.natAdd r q) x)) F) =
      lie E s (toL (Matrix.single p q x)) (sl1 m₁ F) := by
  rw [toL_single_nn]
  exact right_slice_lie_second_block m₁ _ F

theorem left_slice_single_second (F : Sm E (r + s)) {n : ℕ} (b : Fin n → Sm E r) (q : Fin n → Sm E s)
    (hexp : ∀ m : GA E r × GA E s, F.1 (lev (Ad E) r s m) = ∑ i, (b i).1 m.1 * (q i).1 m.2) (p p' : Fin s)
    (x : Cinf E) (m₂ : GA E s) :
    sl0 m₂ (lie E (r + s) (toL (Matrix.single (Fin.natAdd r p) (Fin.natAdd r p') x)) F) =
      ∑ i, (lie E s (toL (Matrix.single p p' x)) (q i)).1 m₂ • b i := by
  rw [toL_single_nn]
  exact left_slice_lie_second_block F b q hexp _ m₂

theorem right_slice_single_first (F : Sm E (r + s)) {n : ℕ} (b : Fin n → Sm E r) (q : Fin n → Sm E s)
    (hexp : ∀ m : GA E r × GA E s, F.1 (lev (Ad E) r s m) = ∑ i, (b i).1 m.1 * (q i).1 m.2) (p p' : Fin r)
    (x : Cinf E) (m₁ : GA E r) :
    sl1 m₁ (lie E (r + s) (toL (Matrix.single (Fin.castAdd s p) (Fin.castAdd s p') x)) F) =
      ∑ i, (lie E r (toL (Matrix.single p p' x)) (b i)).1 m₁ • q i := by
  rw [toL_single_cc]
  exact right_slice_lie_first_block F b q hexp _ m₁

theorem key_left (W : Submodule ℂ (Sm E r)) (hW : IsStable W) (F : Sm E (r + s))
    (hu : ∀ (x : BlockIx (r + s) r → Ad E) g, F.1 (unip x * g) = F.1 g)
    (hP : ∀ m₂, sl0 m₂ F ∈ W) {n : ℕ} (b : Fin n → Sm E r) (q : Fin n → Sm E s) (hb : ∀ i, b i ∈ W)
    (hexp : ∀ m : GA E r × GA E s, F.1 (lev (Ad E) r s m) = ∑ i, (b i).1 m.1 * (q i).1 m.2)
    (X : Lie E (r + s)) (hX : ∀ (i : Fin s) (j : Fin r), X (Fin.natAdd r i) (Fin.castAdd s j) = 0)
    (m₂ : GA E s) : sl0 m₂ (lie E (r + s) X F) ∈ W := by
  rw [lie_sum_single, map_sum]
  refine W.sum_mem fun p _ => ?_
  rw [map_sum]
  refine W.sum_mem fun q' _ => ?_
  induction p using Fin.addCases with
  | left p =>
    induction q' using Fin.addCases with
    | left q' =>
      rw [left_slice_single_first]
      exact hW (.lie _) _ (hP m₂)
    | right q' =>
      have h0 : sl0 m₂ (lie E (r + s) (toL (Matrix.single (Fin.castAdd s p) (Fin.natAdd r q')
          (X (Fin.castAdd s p) (Fin.natAdd r q')))) F) = 0 :=
        Subtype.ext (funext fun m₁ => by rw [left_slice_apply]; exact lie_upper_lev F hu p q' _ (m₁, m₂))
      rw [h0]
      exact W.zero_mem
  | right p =>
    induction q' using Fin.addCases with
    | left q' =>
      rw [hX p q', Matrix.single_zero]
      have : (toL (0 : Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E)) : Lie E (r + s)) = 0 := rfl
      rw [this, map_zero, LinearMap.zero_apply, map_zero]
      exact W.zero_mem
    | right q' =>
      rw [left_slice_single_second F b q hexp]
      exact W.sum_mem fun i _ => W.smul_mem _ (hb i)

theorem key_right (W : Submodule ℂ (Sm E s)) (hW : IsStable W) (F : Sm E (r + s))
    (hu : ∀ (x : BlockIx (r + s) r → Ad E) g, F.1 (unip x * g) = F.1 g)
    (hP : ∀ m₁, sl1 m₁ F ∈ W) {n : ℕ} (b : Fin n → Sm E r) (q : Fin n → Sm E s) (hq : ∀ i, q i ∈ W)
    (hexp : ∀ m : GA E r × GA E s, F.1 (lev (Ad E) r s m) = ∑ i, (b i).1 m.1 * (q i).1 m.2)
    (X : Lie E (r + s)) (hX : ∀ (i : Fin s) (j : Fin r), X (Fin.natAdd r i) (Fin.castAdd s j) = 0)
    (m₁ : GA E r) : sl1 m₁ (lie E (r + s) X F) ∈ W := by
  rw [lie_sum_single, map_sum]
  refine W.sum_mem fun p _ => ?_
  rw [map_sum]
  refine W.sum_mem fun q' _ => ?_
  induction p using Fin.addCases with
  | left p =>
    induction q' using Fin.addCases with
    | left q' =>
      rw [right_slice_single_first F b q hexp]
      exact W.sum_mem fun i _ => W.smul_mem _ (hq i)
    | right q' =>
      have h0 : sl1 m₁ (lie E (r + s) (toL (Matrix.single (Fin.castAdd s p) (Fin.natAdd r q')
          (X (Fin.castAdd s p) (Fin.natAdd r q')))) F) = 0 :=
        Subtype.ext (funext fun m₂ => by rw [right_slice_apply]; exact lie_upper_lev F hu p q' _ (m₁, m₂))
      rw [h0]
      exact W.zero_mem
  | right p =>
    induction q' using Fin.addCases with
    | left q' =>
      rw [hX p q', Matrix.single_zero]
      have : (toL (0 : Matrix (Fin (r + s)) (Fin (r + s)) (Cinf E)) : Lie E (r + s)) = 0 := rfl
      rw [this, map_zero, LinearMap.zero_apply, map_zero]
      exact W.zero_mem
    | right q' =>
      rw [right_slice_single_second]
      exact hW (.lie _) _ (hP m₁)

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockFiniteGeneration
