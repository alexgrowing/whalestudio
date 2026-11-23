import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private def sc {R : Type} [CommRing R] (n : ℕ) : GL (Fin 1) R →* GL (Fin n) R :=
  (GeneralLinearGroup.scalar (Fin n)).comp GeneralLinearGroup.det

private theorem sc_val {R : Type} [CommRing R] (n : ℕ) (x : GL (Fin 1) R) (i j : Fin n) :
    (sc n x).val i j = if i = j then x.val 0 0 else 0 := by
  change Matrix.scalar (Fin n) (Matrix.det x.val) i j = _
  rw [Matrix.det_fin_one]
  by_cases e : i = j <;> simp [e]

private theorem sc_scalar {R : Type} [CommRing R] (n : ℕ) (z : Rˣ) :
    sc n (GeneralLinearGroup.scalar (Fin 1) z) = GeneralLinearGroup.scalar (Fin n) z := by
  ext i j
  rw [sc_val]
  change (if i = j then Matrix.scalar (Fin 1) z.val 0 0 else 0) = Matrix.scalar (Fin n) z.val i j
  by_cases e : i = j <;> simp [e]

private theorem sc_comm {R : Type} [CommRing R] (n : ℕ) (x : GL (Fin 1) R) (g : GL (Fin n) R) :
    sc n x * g = g * sc n x :=
  Units.ext (Matrix.scalar_commute (Matrix.det x.val) (fun _ => Commute.all _ _) g.val).eq

private theorem map_sc {R S : Type} [CommRing R] [CommRing S] (n : ℕ) (p : R →+* S) (x : GL (Fin 1) R) :
    GeneralLinearGroup.map p (sc n x) = sc n (GeneralLinearGroup.map p x) := by
  ext i j
  change p ((sc n x).val i j) = _
  rw [sc_val, sc_val]
  split_ifs
  · rfl
  · exact map_zero p

private theorem corner_sc {R S : Type} [CommRing R] [CommRing S] (n : ℕ) (s : R →ₙ+* S) (x : GL (Fin 1) R) :
    GlobalTheory.CuspRep.cornerGL n s (sc n x) = sc n (GlobalTheory.CuspRep.cornerGL 1 s x) := by
  ext i j
  rw [sc_val]
  change (1 : Matrix (Fin n) (Fin n) S) i j - s ((1 : Matrix (Fin n) (Fin n) R) i j) + s ((sc n x).val i j) =
    if i = j then (1 : Matrix (Fin 1) (Fin 1) S) 0 0 - s ((1 : Matrix (Fin 1) (Fin 1) R) 0 0) + s (x.val 0 0) else 0
  rw [sc_val]
  by_cases e : i = j <;> simp [Matrix.one_apply, e]

private theorem continuous_sc {R : Type} [CommRing R] [TopologicalSpace R] (n : ℕ) :
    Continuous (sc n : GL (Fin 1) R → GL (Fin n) R) := by
  have h : Continuous fun x : GL (Fin 1) R => (sc n x).val := by
    refine continuous_matrix fun i j => ?_
    simp only [sc_val]
    split_ifs
    · exact Units.continuous_val.matrix_elem 0 0
    · exact continuous_const
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  simp only [← map_inv]
  refine continuous_matrix fun i j => ?_
  simp only [sc_val]
  split_ifs
  · exact Units.continuous_coe_inv.matrix_elem 0 0
  · exact continuous_const

private theorem sc_mem {K : Type} [Field K] (n : ℕ) (O : Subring K) (x : GL (Fin 1) K)
    (h : x ∈ Formalism.UG.GLint (Fin 1) O) : sc n x ∈ Formalism.UG.GLint (Fin n) O := by
  rw [GlobalTheory.AdelicU.mem_GLint_iff] at h ⊢
  rw [← map_inv]
  constructor <;> intro i j <;> rw [sc_val] <;> split_ifs
  · exact h.1 0 0
  · exact zero_mem _
  · exact h.2 0 0
  · exact zero_mem _

theorem UpperTheory.V.Af.Smo.centEq :
    UpperTheory.V.Af.Smo.CentLoc → UpperTheory.V.Af.Smo.AwayInd → UpperTheory.V.Af.Smo.DenseAway → UpperTheory.V.Af.Smo.CentEq := by
  intro hL hA hD E _ _ n S B f f' hc hc' hl hl' hE hK hK' z g g'
  have h1 : ∀ k : GL (Fin 1) (Af E), Away S k → ∀ g g' : GA E n,
      f (g * finGL E n (sc n k)) * f' g' = f g * f' (g' * finGL E n (sc n k)) := by
    refine hA E 1 S _ (fun k hk g g' => ?_) (fun w hw k _ _ hP y g g' => ?_)
    · have hk' : InKS S (sc n k) := by
        refine ⟨fun w hw => ?_, fun w => ?_⟩
        · rw [map_sc, hk.1 w hw, map_one]
        · rw [map_sc]; exact sc_mem n _ _ (hk.2 w)
      rw [hK g _ hk', hK' g' _ hk']
    · obtain ⟨c, hcc⟩ := hL E n w (B w) (GeneralLinearGroup.det y)
      have e : sc n (locGL E 1 w y) = locGL E n w (1 * GeneralLinearGroup.scalar (Fin n) (GeneralLinearGroup.det y)) := by
        rw [one_mul]; exact (corner_sc n (sLoc E w) y).symm
      have a := hcc _ ((hE w hw).1 (g * finGL E n (sc n k))) 1
      have b := hcc _ ((hE w hw).2 (g' * finGL E n (sc n k))) 1
      simp only [map_one, mul_one] at a b
      rw [map_mul, map_mul, ← mul_assoc, ← mul_assoc, e, a, b, mul_assoc, hP]
      ring
  have h2 : ∀ x : GA E 1, f (g * sc n x) * f' g' = f g * f' (g' * sc n x) := by
    refine isClosed_property (hD E 1 S).denseRange_val (isClosed_eq ?_ ?_) ?_
    · exact (hc.comp (continuous_const.mul (continuous_sc n))).mul continuous_const
    · exact continuous_const.mul (hc'.comp (continuous_const.mul (continuous_sc n)))
    · rintro ⟨_, γ, k, hk, rfl⟩
      have e : ∀ u : GA E n, u * sc n (ratGL E 1 γ * finGL E 1 k) = ratGL E n (sc n γ) * (u * finGL E n (sc n k)) := by
        intro u
        rw [map_mul, ← mul_assoc, ← sc_comm n (ratGL E 1 γ) u, mul_assoc]
        congr 1
        · exact (map_sc n _ γ).symm
        · exact congrArg _ (corner_sc n (sFin E) k).symm
      change f (g * sc n (ratGL E 1 γ * finGL E 1 k)) * _ = _ * f' (g' * sc n (ratGL E 1 γ * finGL E 1 k))
      rw [e, e]
      have a : ∀ u, f (ratGL E n (sc n γ) * u) = f u := hl _
      have b : ∀ u, f' (ratGL E n (sc n γ) * u) = f' u := hl' _
      rw [a, b]
      exact h1 k hk g g'
  rw [← sc_scalar]
  exact h2 _
