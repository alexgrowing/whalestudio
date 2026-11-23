import Development.EtaleCohomology.KummerTheory.AdicLimPf

noncomputable section
open CategoryTheory GlobalTheory.EtC

namespace LateralTheory.EWeil.AdicFinPf

variable (l : ℕ) [Fact l.Prime] (E : Spc) (n i : ℤ)

instance neZeroPow (k : ℕ) : NeZero (l ^ k) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩

def levHom (k : ℕ) : Hl l E n i →+ Ht (l ^ k) E n i where
  toFun x := LateralTheory.KummerTheory.lev l x k
  map_zero' := rfl
  map_add' _ _ := rfl

theorem lev_smul (k : ℕ) (r : ℤ_[l]) (x : Hl l E n i) :
    LateralTheory.KummerTheory.lev l (r • x) k = PadicInt.toZModPow k r • LateralTheory.KummerTheory.lev l x k := rfl

theorem lev_red (k : ℕ) (x : Hl l E n i) :
    red (l ^ (k + 1)) (l ^ k) E n i (LateralTheory.KummerTheory.lev l x (k + 1)) = LateralTheory.KummerTheory.lev l x k := x.2 k

theorem red_smul {Q q : ℕ} [NeZero Q] [NeZero q] (h : q ∣ Q) (c : ZMod Q) (z : Ht Q E n i) :
    red Q q E n i (c • z) = ZMod.castHom h (ZMod q) c • red Q q E n i z := by
  conv_lhs => rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul, map_nsmul]
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, Nat.cast_smul_eq_nsmul]

open LateralTheory.KummerTheory in

theorem gen_mod {ι : Type*} (g : ι → Hl l E n i)
    (hg : ∀ x : Hl l E n i, ∃ t y, x = g t + ((l : ℤ_[l]) ^ 1) • y) :
    ∀ (k : ℕ) (x : Hl l E n i), ∃ m ∈ Submodule.span ℤ_[l] (Set.range g), ∃ y, x = m + ((l : ℤ_[l]) ^ k) • y := by
  intro k
  induction k with
  | zero => intro x; exact ⟨0, Submodule.zero_mem _, x, by simp⟩
  | succ k ih =>
    intro x
    obtain ⟨m, hm, y, rfl⟩ := ih x
    obtain ⟨t, y', rfl⟩ := hg y
    refine ⟨m + ((l : ℤ_[l]) ^ k) • g t, Submodule.add_mem _ hm (Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, rfl⟩)), y', ?_⟩
    rw [smul_add, smul_smul, ← pow_add, add_assoc]

theorem lev_pow_smul (k : ℕ) (y : Hl l E n i) : LateralTheory.KummerTheory.lev l (((l : ℤ_[l]) ^ k) • y) k = 0 := by
  rw [lev_smul, map_pow, map_natCast, ← Nat.cast_pow, ZMod.natCast_self, zero_smul]

theorem AdicFin_of : LateralTheory.KummerTheory.AdicFin := by
  intro l _ E n i hfin hker
  classical

  let S : Set (Ht (l ^ 1) E n i) := Set.range fun x : Hl l E n i => LateralTheory.KummerTheory.lev l x 1
  haveI : Finite (Ht (l ^ 1) E n i) := hfin 1
  haveI : Fintype S := Fintype.ofFinite S
  let g : S → Hl l E n i := fun s => s.2.choose
  have hgs : ∀ s : S, LateralTheory.KummerTheory.lev l (g s) 1 = s.1 := fun s => s.2.choose_spec
  have hg : ∀ x : Hl l E n i, ∃ t y, x = g t + ((l : ℤ_[l]) ^ 1) • y := by
    intro x
    refine ⟨⟨_, x, rfl⟩, ?_⟩
    obtain ⟨y, hy⟩ := hker 1 (x - g ⟨_, x, rfl⟩) (by
      change levHom l E n i 1 (x - _) = 0
      rw [map_sub]; exact sub_eq_zero.mpr (hgs ⟨_, x, rfl⟩).symm)
    exact ⟨y, by rw [← hy]; abel⟩
  rw [Module.finite_def, Submodule.fg_def]
  refine ⟨Set.range g, Set.finite_range g, eq_top_iff.mpr fun x _ => ?_⟩

  let T : ℕ → Type 1 := fun k => {a : S → ZMod (l ^ k) //
    LateralTheory.KummerTheory.lev l x k = ∑ t, a t • LateralTheory.KummerTheory.lev l (g t) k}
  have hT : ∀ k (a : T (k + 1)), LateralTheory.KummerTheory.lev l x k =
      ∑ t, ZMod.castHom (pow_dvd_pow l (Nat.le_succ k)) (ZMod (l ^ k)) (a.1 t) • LateralTheory.KummerTheory.lev l (g t) k := by
    intro k a
    refine (lev_red l E n i k x).symm.trans ((congrArg _ a.2).trans ?_)
    rw [map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [red_smul _ _ _ (pow_dvd_pow l (Nat.le_succ k)), lev_red]
  let f : ∀ k, T (k + 1) ⟶ T k := fun k => TypeCat.ofHom fun a =>
    (⟨fun t => ZMod.castHom (pow_dvd_pow l (Nat.le_succ k)) (ZMod (l ^ k)) (a.1 t), hT k a⟩ : T k)
  let F : ℕᵒᵖ ⥤ Type 1 := Functor.ofOpSequence f
  haveI : ∀ j : ℕᵒᵖ, Finite (F.obj j) := fun j => by
    change Finite (T j.unop); exact Subtype.finite
  haveI : ∀ j : ℕᵒᵖ, Nonempty (F.obj j) := fun j => by
    change Nonempty (T j.unop)
    obtain ⟨m, hm, y, rfl⟩ := gen_mod l E n i g hg j.unop x
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ_[l]).mp hm
    refine ⟨⟨fun t => PadicInt.toZModPow j.unop (c t), ?_⟩⟩
    change levHom l E n i _ (_ + _) = _
    rw [map_add, map_sum, show levHom l E n i j.unop (((l : ℤ_[l]) ^ j.unop) • y) = 0 from lev_pow_smul l E n i _ y, add_zero]
    rfl
  obtain ⟨sec, hsec⟩ := nonempty_sections_of_finite_inverse_system F
  let A : ∀ k, T k := fun k => sec (Opposite.op k)
  have hA : ∀ k t, ZMod.castHom (pow_dvd_pow l (Nat.le_succ k)) (ZMod (l ^ k)) ((A (k + 1)).1 t) = (A k).1 t := by
    intro k t
    have := hsec (homOfLE (Nat.le_add_right k 1)).op
    rw [Functor.ofOpSequence_map_homOfLE_succ] at this
    refine Eq.trans ?_ (congrArg (fun b : T k => b.1 t) this)
    rfl
  have hdiv : ∀ t j, (l : ℤ) ^ j ∣ (((A (j + 1)).1 t).val : ℤ) - (((A j).1 t).val : ℤ) := by
    intro t j
    have h := hA j t
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, ← ZMod.natCast_zmod_val ((A j).1 t)] at h
    have h2 : ((((A j).1 t).val : ℤ) : ZMod (l ^ j)) = ((((A (j + 1)).1 t).val : ℤ) : ZMod (l ^ j)) := by
      simp only [Int.cast_natCast]; exact h.symm
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h2
    exact_mod_cast h2
  let α : S → ℤ_[l] := fun t => PadicInt.ofIntSeq _
    (PadicInt.isCauSeq_padicNorm_of_pow_dvd_sub (fun j => (((A j).1 t).val : ℤ)) l (hdiv t))
  have hα : ∀ k t, PadicInt.toZModPow k (α t) = (A k).1 t := by
    intro k t
    rw [PadicInt.toZModPow_ofIntSeq_of_pow_dvd_sub _ _ (hdiv t), Int.cast_natCast, ZMod.natCast_zmod_val]
  refine (Submodule.mem_span_range_iff_exists_fun ℤ_[l]).mpr ⟨α, Subtype.ext (funext fun k => ?_)⟩
  change levHom l E n i k (∑ t, α t • g t) = LateralTheory.KummerTheory.lev l x k
  rw [map_sum, (A k).2]
  refine Finset.sum_congr rfl fun t _ => ?_
  change LateralTheory.KummerTheory.lev l (α t • g t) k = _
  rw [lev_smul, hα]

end LateralTheory.EWeil.AdicFinPf
