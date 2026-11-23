import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.LevelSAllOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.MulVecSpanStable

noncomputable section

namespace PI.LevelKSplit.W.Glob

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain PI.LevelKSplit
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

def covR (x : Fin n → E) : Fin n → R ⊗[F] E := fun j => inclR R (∑ i, σ (x i) * J i j)

theorem sigR_inclR (a : E) : sigR R σ (inclR R a) = inclR R (σ a) := by
  simp [sigR, inclR]

theorem hR_ratV_left (x : Fin n → E) (y : Fin n → R ⊗[F] E) :
    hR R σ J (ratV (F := F) R x) y = covR R σ J x ⬝ᵥ y := by
  simp only [hR, Formalism.UG.hform, covR, ratV, JR, Matrix.map_apply, sigR_inclR, dotProduct,
    map_sum, map_mul, Finset.sum_mul]
  exact Finset.sum_comm

theorem covR_ratV (x y : Fin n → E) :
    covR R σ J x ⬝ᵥ ratV (F := F) R y = inclR R (hE σ J x y) := by
  simp only [covR, ratV, hE, Formalism.UG.hform, dotProduct, Finset.sum_mul, map_sum, map_mul]
  exact Finset.sum_comm

theorem ratV_add (x y : Fin n → E) :
    ratV (F := F) R (x + y) = ratV (F := F) R x + ratV (F := F) R y := by
  funext i
  simp [ratV]

theorem ratV_smul (c : E) (x : Fin n → E) :
    ratV (F := F) R (c • x) = inclR (F := F) R c • ratV (F := F) R x := by
  funext i
  simp [ratV, smul_eq_mul, map_mul]

theorem ratV_zero : ratV (F := F) R (0 : Fin n → E) = 0 := by
  funext i
  simp [ratV]

variable {R σ J}

theorem ratV_mem_span {m : ℕ} (Y : Fin m → Fin n → E) (x : Fin n → E)
    (hx : x ∈ Submodule.span E (Set.range Y)) :
    ratV (F := F) R x ∈ Submodule.span (R ⊗[F] E) (Set.range fun a => ratV (F := F) R (Y a)) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    exact Submodule.subset_span ⟨a, rfl⟩
  | zero => rw [ratV_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [ratV_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [ratV_smul]; exact Submodule.smul_mem _ _ hy

theorem lin_fix_span (g : HA R σ J) {m : ℕ} (Y : Fin m → Fin n → E)
    (hY : ∀ a, lin R σ J g (ratV (F := F) R (Y a)) = ratV (F := F) R (Y a))
    (y : Fin n → R ⊗[F] E)
    (hy : y ∈ Submodule.span (R ⊗[F] E) (Set.range fun a => ratV (F := F) R (Y a))) :
    lin R σ J g y = y := by
  induction hy using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨a, rfl⟩ := hw
    exact hY a
  | zero => exact map_zero _
  | add w w' _ _ hw hw' => rw [map_add, hw, hw']
  | smul c w _ hw => rw [map_smul, hw]

theorem spanR_univ {m : ℕ} (Y : Fin m → Fin n → E) :
    spanR (F := F) R Y Set.univ =
      Submodule.span (R ⊗[F] E) (Set.range fun a => ratV (F := F) R (Y a)) := by
  simp only [spanR, Set.image_univ]

theorem hE_swap (hJ : IsHermND σ J) (hinv : ∀ x, σ (σ x) = x) (x y : Fin n → E) :
    hE σ J y x = σ (hE σ J x y) := by
  simp only [hE, Formalism.UG.hform, map_sum, map_mul, AlgHom.coe_toRingHom, RingHom.coe_coe, hinv, hJ.1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem H_fix_e {r : ℕ} (P : Frame E n r) (k : HA R σ J) (hk : k ∈ Hsub R σ J P) (a : Fin r) :
    lin R σ J k (ratV (F := F) R (P.e a)) = ratV (F := F) R (P.e a) := by
  rw [Hsub, mem_stabT] at hk
  simpa [tupH, F0, Fin.append_left, Fin.snoc_castSucc] using hk (Fin.castAdd r (Fin.castSucc a))

theorem H_fix_f {r : ℕ} (P : Frame E n r) (k : HA R σ J) (hk : k ∈ Hsub R σ J P) (a : Fin r) :
    lin R σ J k (ratV (F := F) R (P.f a)) = ratV (F := F) R (P.f a) := by
  rw [Hsub, mem_stabT] at hk
  simpa [tupH, Fin.append_right] using hk (Fin.natAdd (r + 1) a)

theorem H_perp {r : ℕ} (P : Frame E n r) (k : HA R σ J) (hk : k ∈ Hsub R σ J P) (w : Fin n → E)
    (hw : ∀ a, hE σ J (P.e a) w = 0 ∧ hE σ J (P.f a) w = 0) (b : Fin r) :
    covR R σ J (P.e b) ⬝ᵥ lin R σ J k (ratV (F := F) R w) = 0 ∧
      covR R σ J (P.f b) ⬝ᵥ lin R σ J k (ratV (F := F) R w) = 0 := by
  have key : ∀ u : Fin n → E, lin R σ J k (ratV (F := F) R u) = ratV (F := F) R u →
      hE σ J u w = 0 → covR R σ J u ⬝ᵥ lin R σ J k (ratV (F := F) R w) = 0 := by
    intro u hu h0
    calc covR R σ J u ⬝ᵥ lin R σ J k (ratV (F := F) R w)
        = hR R σ J (lin R σ J k (ratV (F := F) R u)) (lin R σ J k (ratV (F := F) R w)) := by
          rw [hu, hR_ratV_left]
      _ = hR R σ J (ratV (F := F) R u) (ratV (F := F) R w) := by rw [hR_lin]
      _ = 0 := by rw [hR_ratV_left, covR_ratV, h0, map_zero]
  exact ⟨key _ (H_fix_e P k hk b) (hw b).1, key _ (H_fix_f P k hk b) (hw b).2⟩

end Gen

section Loc

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

def phiV (v : HeightOneSpectrum (𝓞 F)) : Af F ⊗[F] E →+* Fv F v ⊗[F] E :=
  (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)).toRingHom

theorem phiV_inclR (v : HeightOneSpectrum (𝓞 F)) (a : E) :
    phiV v (inclR (Af F) a) = inclR (Fv F v) a := by
  simp [phiV, inclR]

theorem phiV_ratV (v : HeightOneSpectrum (𝓞 F)) (x : Fin n → E) :
    (fun i => phiV v (ratV (F := F) (Af F) x i)) = ratV (F := F) (Fv F v) x := by
  funext i
  exact phiV_inclR v (x i)

theorem phiV_cov (v : HeightOneSpectrum (𝓞 F)) (x : Fin n → E) (y : Fin n → Af F ⊗[F] E) :
    phiV v (covR (Af F) σ J x ⬝ᵥ y) = covR (Fv F v) σ J x ⬝ᵥ fun i => phiV v (y i) := by
  simp only [dotProduct, map_sum, map_mul, covR, phiV_inclR]

theorem phiV_span (v : HeightOneSpectrum (𝓞 F)) {m : ℕ} (Y : Fin m → Fin n → E)
    (y : Fin n → Af F ⊗[F] E) (hy : y ∈ spanR (F := F) (Af F) Y Set.univ) :
    (fun i => phiV v (y i)) ∈
      Submodule.span (Fv F v ⊗[F] E) (Set.range fun a => ratV (F := F) (Fv F v) (Y a)) := by
  rw [spanR_univ] at hy
  induction hy using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨a, rfl⟩ := hw
    rw [phiV_ratV]
    exact Submodule.subset_span ⟨a, rfl⟩
  | zero =>
    have h0 : (fun i => phiV v ((0 : Fin n → Af F ⊗[F] E) i)) = 0 := by
      funext i; simp
    rw [h0]; exact Submodule.zero_mem _
  | add w w' _ _ hw hw' =>
    have h1 : (fun i => phiV v ((w + w') i)) = (fun i => phiV v (w i)) + fun i => phiV v (w' i) := by
      funext i; simp
    rw [h1]; exact Submodule.add_mem _ hw hw'
  | smul c w _ hw =>
    have h1 : (fun i => phiV v ((c • w) i)) = phiV v c • fun i => phiV v (w i) := by
      funext i; simp
    rw [h1]; exact Submodule.smul_mem _ _ hw

theorem compV_mulVec (v : HeightOneSpectrum (𝓞 F)) (g : HA (Af F) σ J) (x : Fin n → Af F ⊗[F] E) :
    Matrix.mulVec ((compV v (incAf σ J g) : GL (Fin n) (Fv F v ⊗[F] E)) :
      Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) (fun i => phiV v (x i)) =
      fun i => phiV v (lin (Af F) σ J g x i) := by
  funext i
  exact (RingHom.map_mulVec (phiV v)
    (HA.mat (R := Af F) (σ := σ) (J := J) g : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) x i).symm

theorem mem_Kf (Λ : Set (Fin n → E)) (g : HA (Af F) σ J) :
    g ∈ Kf σ J Λ ↔ ∀ v, ∀ x, x ∈ latLoc (E := E) v Λ ↔
      Matrix.mulVec ((compV v (incAf σ J g) : GL (Fin n) (Fv F v ⊗[F] E)) :
        Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) x ∈ latLoc (E := E) v Λ := by
  simp only [Kf, Subgroup.mem_iInf, Subgroup.mem_comap, MonoidHom.coe_comp, Function.comp_apply] <;>
    exact Iff.rfl

end Loc

end PI.LevelKSplit.W.Glob
