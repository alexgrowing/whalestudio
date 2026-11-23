import Development.EtaleCohomology.EtaleTrace.LFinCut
import Development.EtaleCohomology.KummerTheory.FinBock
import Development.EtaleCohomology.WeilConjectures.AdicFinPf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.OneMul
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SplitsSelfOfIso

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace UpperTheory.Gal.Int.Geo

private theorem red_pow_add_apply_eq (hA : A11) (l : ℕ) [Fact (Nat.Prime l)] (E : Spc) (n i : ℤ)
    (x : Hl l E n i) (m a : ℕ) :
    red (l ^ (m + a)) (l ^ m) E n i ((x : (j : ℕ) → HtL l j E n i) (m + a)) =
      (x : (j : ℕ) → HtL l j E n i) m := by
  have hl : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have hx : ∀ k : ℕ, red (l ^ (k + 1)) (l ^ k) E n i ((x : (j : ℕ) → HtL l j E n i) (k + 1)) =
      (x : (j : ℕ) → HtL l j E n i) k := x.2
  induction a with
  | zero =>
    haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ hl⟩
    exact (hA (l ^ m) (l ^ m) dvd_rfl E).2.2.1 n i _
  | succ a ih =>
    haveI : NeZero (l ^ (m + (a + 1))) := ⟨pow_ne_zero _ hl⟩
    have h4 := (hA (l ^ (m + (a + 1))) (l ^ (m + a)) (pow_dvd_pow l (by omega)) E).2.2.2 (l ^ m)
      (pow_dvd_pow l (by omega)) n i ((x : (j : ℕ) → HtL l j E n i) (m + (a + 1)))
    rw [← h4]
    exact (congrArg (red (l ^ (m + a)) (l ^ m) E n i) (hx (m + a))).trans ih

private theorem red_pow_apply_eq_of_le (hA : A11) (l : ℕ) [Fact (Nat.Prime l)] (E : Spc) (n i : ℤ)
    (x : Hl l E n i) (m M : ℕ) (h : m ≤ M) :
    red (l ^ M) (l ^ m) E n i ((x : (j : ℕ) → HtL l j E n i) M) = (x : (j : ℕ) → HtL l j E n i) m := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le h
  exact red_pow_add_apply_eq hA l E n i x m a

private theorem exists_eq_pow_smul_of_lev_eq_zero (hA : A11) (l : ℕ) [Fact (Nat.Prime l)] (E : Spc) (n i : ℤ)
    (hf : ∀ m : ℕ, Finite (Ht (l ^ m) E n i)) (hB : ∀ b : ℕ, LateralTheory.KummerTheory.BockData l b E i) (b : ℕ)
    (x : Hl l E n i) (hx : LateralTheory.KummerTheory.lev l x b = 0) : ∃ y : Hl l E n i, x = (l : ℤ_[l]) ^ b • y := by
  obtain ⟨u, d, hud⟩ := hB b
  let xs : (j : ℕ) → HtL l j E n i := x
  have hmem : ∀ k : ℕ, red (l ^ (k + 1)) (l ^ k) E n i (xs (k + 1)) = xs k := x.2
  let S : ℕ → Type 1 := fun a => {z : Ht (l ^ a) E n i // u a n z = xs (b + a)}
  have hS : ∀ (a : ℕ) (z : S (a + 1)), u a n (red (l ^ (a + 1)) (l ^ a) E n i z.1) = xs (b + a) := by
    intro a z
    rw [← (hud a n).2.2.2.2.2 z.1, z.2]
    exact hmem (b + a)
  let F : ℕᵒᵖ ⥤ Type 1 :=
    Functor.ofOpSequence (X := S) (fun a => TypeCat.ofHom (fun z => ⟨_, hS a z⟩ : S (a + 1) → S a))
  haveI : ∀ j : ℕᵒᵖ, Finite (F.obj j) := fun j => by
    show Finite (S j.unop)
    haveI := hf j.unop
    exact Subtype.finite
  haveI : ∀ j : ℕᵒᵖ, Nonempty (F.obj j) := fun j => by
    show Nonempty (S j.unop)
    obtain ⟨z, hz⟩ := ((hud j.unop n).1 (xs (b + j.unop))).1
      (by rw [red_pow_apply_eq_of_le hA l E n i x b (b + j.unop) (by omega)]; exact hx)
    exact ⟨⟨z, hz⟩⟩
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_inverse_system F
  let ys : (j : ℕ) → HtL l j E n i := fun j => (s (Opposite.op j)).1
  have hy : ys ∈ HlSub l E n i := by
    show ∀ k : ℕ, red (l ^ (k + 1)) (l ^ k) E n i (ys (k + 1)) = ys k
    intro k
    have := hs (homOfLE (Nat.le_succ k)).op
    rw [Functor.ofOpSequence_map_homOfLE_succ] at this
    exact congrArg Subtype.val this
  refine ⟨⟨ys, hy⟩, ?_⟩
  apply Subtype.ext
  funext m
  show xs m = ((l : ℤ_[l]) ^ b • ys) m
  rw [Pi.smul_apply, show (l : ℤ_[l]) ^ b = ((l ^ b : ℕ) : ℤ_[l]) by push_cast; rfl,
    Nat.cast_smul_eq_nsmul]
  have hym : red (l ^ (b + m)) (l ^ m) E n i (ys (b + m)) = ys m :=
    red_pow_apply_eq_of_le hA l E n i ⟨ys, hy⟩ m (b + m) (by omega)
  have h5 : u m n (ys m) = xs (b + m) := (s (Opposite.op m)).2
  rw [← hym]
  erw [← map_nsmul]
  erw [← (hud m n).2.2.2.1 (ys (b + m))]
  erw [hym, h5]
  exact (red_pow_apply_eq_of_le hA l E n i x m (b + m) (by omega)).symm

theorem vFin_of (h : KunnethLefschetz.In) : GlobalTheory.GalV.VFin := by
  intro l _ k _ _ hl X p _ n i
  have hInv : GlobalTheory.EtC.Inv l (sch.obj X) := by
    intro U hU
    obtain ⟨f⟩ := hU
    have g : U ⟶ X := f
    have := hl.map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (g ≫ p).appTop).hom
    simpa using this
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have hfin : ∀ m : ℕ, Finite (Ht (l ^ m) (sch.obj X) n i) := by
    intro m
    haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ hl0⟩
    exact h.e4 (l ^ m) k (by push_cast; exact hl.pow m) p n i
  have hM : Module.Finite ℤ_[l] (Hl l (sch.obj X) n i) :=
    LateralTheory.EWeil.AdicFinPf.AdicFin_of l (sch.obj X) n i hfin
      (fun b x hx => exists_eq_pow_smul_of_lev_eq_zero h.a11 l (sch.obj X) n i hfin
        (fun b' => LateralTheory.Fin.Bock.etale_bockstein_sequence_adic_finiteness h.a7 h.a8 h.a10 h.a11 l b' (sch.obj X) i hInv) b x hx)
  exact ⟨hM, Module.Finite.base_change ℤ_[l] ℚ_[l] _⟩

end UpperTheory.Gal.Int.Geo

end
