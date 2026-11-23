import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.FaceRes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexDifferentialValuesStatement

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC LateralTheory.CohomologicalPurity LateralTheory.CohomologicalPurity.TubeCut UpperTheory.Et.Prd

private theorem map_res' {E E' : Spc} (j : E ⟶ E') {p : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (z : Sx E p U) :
    (z.map j).res g = (z.res g).map j := by
  exact (FunctorToTypes.naturality (j.app _) g.op z).symm

private theorem map_face' {E E' : Spc} (j : E ⟶ E') {p : ℕ} {U : Scheme.{0}} (z : Sx E (p + 1) U) (i : Fin (p + 2)) :
    (z.map j).face i = (z.face i).map j :=
  (ConcreteCategory.congr_hom (NatTrans.congr_app (j.naturality (SimplexCategory.δ i).op) (op U)) z).symm

private theorem ev_delta_zero {R : Type} [CommRing R] {E : Spc} {I : Cx R} {N M s t : ℤ} (hm : N + 1 = M)
    (α : Cochain ((chains R).obj E) I N) (U : Scheme.{0}) (x : Sx E 0 U)
    (ht : -((0 : ℕ) : ℤ) + M = t) (hs : -((0 : ℕ) : ℤ) + N = s) :
    ev (δ N M α) 0 t ht U x = Sec.map (I.d s t) (ev α 0 s hs U x) := by
  obtain rfl : t = M := by omega
  obtain rfl : s = N := by omega
  exact (GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values R hm α U).1 x

private theorem fam_smul_apply {R : Type} [CommRing R] {E : Spc} {Z : Sub E} {p : ℕ} {M : Shv R} (u : ℤˣ) (a : Fam Z p M)
    (U : Scheme.{0}) (z : Sx E p U) : (u • a).1 U z = u • a.1 U z := by
  rfl

theorem UpperTheory.supportDoubleComplex_total_represents_vanishing_cochain :
    ∀ (R : Type) [CommRing R] {E E' : Spc} (j : E ⟶ E') (Z : Sub E) (K : Cx R) (m n N : ℤ), n + m = N →
    (∀ γ : Cochain ((chains R).obj E') K N, (∀ (p : ℕ) (s : ℤ) h (U : Scheme.{0}) (z : Sx E p U), Z.mem p U z → ev γ p s h U (z.map j) = 0) → ∃ x : (famDC Z K m).Tot, (famDC Z K m).Deg n x ∧ Comp j γ x) ∧
    (∀ (γ : Cochain ((chains R).obj E') K N) (x x' : (famDC Z K m).Tot), (famDC Z K m).Deg n x → (famDC Z K m).Deg n x' → Comp j γ x → Comp j γ x' → x = x') ∧
    (∀ (γ : Cochain ((chains R).obj E') K N) (x : (famDC Z K m).Tot), Comp j γ x → Comp j (δ N (N + 1) γ) ((famDC Z K m).D n x)) ∧
    (∀ (γ γ' : Cochain ((chains R).obj E') K N) (x x' : (famDC Z K m).Tot), Comp j γ x → Comp j γ' x' → Comp j (γ - γ') (x - x')) ∧
    ∀ x : (famDC Z K m).Tot, (famDC Z K m).Deg n x → (famDC Z K m).Deg (n + 1) ((famDC Z K m).D n x) := by
  intro R _ E E' j Z K m n N hN
  have ev_nat := (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E') (I := K) (n := N)).2.1
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro γ hγ
    let x : (famDC Z K m).Tot := fun p s =>
      if h : -(p : ℤ) + N = s + m then
        (⟨fun U z => ev γ p (s + m) h U (z.map j),
          ⟨fun V U g z => (ev_nat γ p (s + m) h V U g (z.map j)).trans (by rw [map_res']),
           fun U z hz => hγ p (s + m) h U z hz⟩⟩ : Fam Z p (K.X (s + m)))
      else 0
    refine ⟨x, fun p s hps => ?_, fun p s h U z => ?_⟩
    · have h : ¬ (-(p : ℤ) + N = s + m) := by omega
      exact dif_neg h
    · exact congrArg (fun a : Fam Z p (K.X (s + m)) =>
        (a : (U : Scheme.{0}) → Sx E p U → Sec (K.X (s + m)) U) U z) (dif_pos h)
  · intro γ x x' hx hx' cx cx'
    funext p s
    by_cases hps : (p : ℤ) + s = n
    · have h : -(p : ℤ) + N = s + m := by omega
      change (x p s : Fam Z p (K.X (s + m))) = x' p s
      apply Subtype.ext
      funext U z
      exact (cx p s h U z).trans (cx' p s h U z).symm
    · rw [hx p s hps, hx' p s hps]
  · intro γ x cx p s h U z
    rcases p with _ | p
    · have h0 : -((0 : ℕ) : ℤ) + N = (s - 1) + m := by omega
      rw [ev_delta_zero (s := s - 1 + m) rfl γ U (z.map j) h h0, ← cx 0 (s - 1) h0 U z]
      rfl
    · have hs : -((p + 1 : ℕ) : ℤ) + N = (s - 1) + m := by omega
      have hp : -(p : ℤ) + N = s + m := by omega
      rw [(GlobalTheory.T.etaleCochainEvalOnSimplex_differential_values R (rfl : N + 1 = N + 1) γ U).2 p (s - 1 + m) (s + m) hs h (z.map j),
        ← cx (p + 1) (s - 1) hs U z]
      simp only [map_face']
      rw [Finset.sum_congr rfl (fun i _ => by rw [← cx p s hp U (z.face i)])]
      have eN : (N + 1).negOnePow = (n + 1).negOnePow * m.negOnePow := by
        rw [← Int.negOnePow_add]; congr 1; omega
      have e2 := fam_smul_apply (n + 1).negOnePow
        (Fam.δ Z p (K.X (s + m)) m.negOnePow (x p s : Fam Z p (K.X (s + m)))) U z
      rw [eN, mul_smul]
      show Sec.map (K.d (s - 1 + m) (s + m)) ((x (p + 1) (s - 1) : Fam Z (p + 1) (K.X (s - 1 + m))).1 U z) +
        ((n + 1).negOnePow • Fam.δ Z p (K.X (s + m)) m.negOnePow (x p s : Fam Z p (K.X (s + m)))).1 U z = _
      rw [e2]
      rfl
  · intro γ γ' x x' cx cx' p s h U z
    rw [((GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E') (I := K) (n := N)).1 γ γ' p (s + m) h U (z.map j)).2.1,
      ← cx p s h U z, ← cx' p s h U z]
    rfl
  · intro x hx p s hps
    rcases p with _ | p
    · have h1 : ((0 : ℕ) : ℤ) + (s - 1) ≠ n := by omega
      show (Fam.map Z 0 (K.d (s - 1 + m) (s + m))) (x 0 (s - 1)) = 0
      rw [hx 0 (s - 1) h1]
      exact map_zero _
    · have h1 : ((p + 1 : ℕ) : ℤ) + (s - 1) ≠ n := by omega
      have h2 : (p : ℤ) + s ≠ n := by omega
      show (Fam.map Z (p + 1) (K.d (s - 1 + m) (s + m))) (x (p + 1) (s - 1)) +
        (n + 1).negOnePow • (Fam.δ Z p (K.X (s + m)) m.negOnePow) (x p s) = 0
      rw [hx _ _ h1, hx _ _ h2]
      show (Fam.map Z (p + 1) (K.d (s - 1 + m) (s + m))) (0 : Fam Z (p + 1) (K.X (s - 1 + m))) +
        (n + 1).negOnePow • (Fam.δ Z p (K.X (s + m)) m.negOnePow) (0 : Fam Z p (K.X (s + m))) = 0
      rw [map_zero, map_zero, smul_zero, add_zero]
