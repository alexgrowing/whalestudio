import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.Ex.TateLimit

theorem exists_finite_reps (L : Type) [AddCommGroup L] [Module.Finite ℤ L] {M : ℕ} (hM : 0 < M) :
    ∃ (A : Type) (_ : Finite A) (r : A → L), ∀ a, ∃ x b, a = r x + M • b := by
  let N : Submodule ℤ L := LinearMap.range ((M : ℤ) • (LinearMap.id : L →ₗ[ℤ] L))
  have hfin : Finite (L ⧸ N) := by
    refine Module.finite_of_fg_torsion _ fun x => ⟨⟨(M : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hM.ne')⟩, ?_⟩
    obtain ⟨y, rfl⟩ := N.mkQ_surjective x
    change (M : ℤ) • N.mkQ y = 0
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨y, rfl⟩
  refine ⟨L ⧸ N, hfin, Quotient.out, fun a => ⟨Submodule.Quotient.mk a, ?_⟩⟩
  have h : a - Quotient.out (Submodule.Quotient.mk a : L ⧸ N) ∈ N :=
    (Submodule.Quotient.eq N).1 (Quotient.out_eq (Submodule.Quotient.mk a : L ⧸ N)).symm
  obtain ⟨b, hb⟩ := h
  refine ⟨b, ?_⟩
  have : M • b = a - Quotient.out (Submodule.Quotient.mk a : L ⧸ N) := by
    rw [← hb]; simp
  rw [this]; abel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
  {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}

theorem ev_add_nsmul (I : TateIso D k Q act e) {M : ℕ} (hM : 0 < M) (a b : D.La) : I.ev M (a + M • b) = I.ev M a := by
  rw [I.add, (I.ker M hM _).2 ⟨b, rfl⟩, _root_.mul_one]

theorem finite_level {M : ℕ} (hM : 0 < M) :
    (Set.range fun I : TateIso D k Q act e => (I.ev M, I.ζ M)).Finite := by
  rcases isEmpty_or_nonempty (TateIso D k Q act e) with h | ⟨⟨I₀⟩⟩
  · exact Set.finite_range _
  haveI := D.fin
  haveI : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
  obtain ⟨A, hA, r, hr⟩ := exists_finite_reps D.La hM
  have hT : {x : Q | x ^ M = 1}.Finite := by
    refine (Set.finite_range fun x => I₀.ev M (r x)).subset fun x hx => ?_
    obtain ⟨a, rfl⟩ := (I₀.onto M hM x).1 hx
    obtain ⟨y, b, rfl⟩ := hr a
    exact ⟨y, (ev_add_nsmul I₀ hM _ _).symm⟩
  have h₁ : (Set.range fun I : TateIso D k Q act e => I.ev M).Finite := by
    refine Set.Finite.of_finite_image (f := fun f => f ∘ r) ?_ ?_
    · refine (Set.Finite.pi' fun _ : A => hT).subset ?_
      rintro _ ⟨_, ⟨I, rfl⟩, rfl⟩ x
      exact (I.onto M hM _).2 ⟨_, rfl⟩
    · rintro _ ⟨I, rfl⟩ _ ⟨J, rfl⟩ h
      funext a
      obtain ⟨y, b, rfl⟩ := hr a
      simp only [ev_add_nsmul _ hM]
      exact congrFun h y
  have h₂ : (Set.range fun I : TateIso D k Q act e => I.ζ M).Finite := by
    haveI : NeZero M := ⟨hM.ne'⟩
    have hfin : Finite (rootsOfUnity M k) := inferInstance
    refine Set.Finite.subset (s := (rootsOfUnity M k : Set kˣ)) hfin ?_
    rintro _ ⟨I, rfl⟩
    exact (I.ζ_prim M hM).pow_eq_one
  refine (h₁.prod h₂).subset ?_
  rintro _ ⟨I, rfl⟩
  exact ⟨⟨I, rfl⟩, ⟨I, rfl⟩⟩

theorem exists_limit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ∀ (k : Type) [Field k] (Q : Type) [Group Q] (act : 𝓞 E → Q → Q) (e : ℕ → Q → Q → kˣ → Prop) (I : ℕ → TateIso D k Q act e), ∃ I' : TateIso D k Q act e, ∀ M, 0 < M → ∀ j₀, ∃ j, j₀ ≤ j ∧ I'.ev M = (I j).ev M ∧ I'.ζ M = (I j).ζ M := by
  intro E _ _ _ H D k _ Q _ act e I
  let U : Ultrafilter ℕ := Filter.hyperfilter ℕ
  have key : ∀ M, ∃ p : (D.La → Q) × kˣ, (∃ j, p.1 = (I j).ev M) ∧
      (0 < M → ∀ᶠ j in (U : Filter ℕ), p.1 = (I j).ev M ∧ p.2 = (I j).ζ M) := by
    intro M
    rcases Nat.eq_zero_or_pos M with rfl | hM
    · exact ⟨((I 0).ev 0, 1), ⟨0, rfl⟩, fun h => absurd h (lt_irrefl _)⟩
    obtain ⟨p, -, hp⟩ := Ultrafilter.eq_pure_of_finite_mem (f := U.map fun j => ((I j).ev M, (I j).ζ M))
      (finite_level (D := D) (act := act) (e := e) hM)
      (Ultrafilter.mem_map.2 (Filter.univ_mem' fun j => ⟨I j, rfl⟩))
    have h : ∀ᶠ j in (U : Filter ℕ), p.1 = (I j).ev M ∧ p.2 = (I j).ζ M := by
      have : {p} ∈ U.map fun j => ((I j).ev M, (I j).ζ M) := by rw [hp]; exact Ultrafilter.mem_pure.2 rfl
      filter_upwards [Ultrafilter.mem_coe.2 (Ultrafilter.mem_map.1 this)] with j hj
      have hj' : ((I j).ev M, (I j).ζ M) = p := hj
      rw [← hj']; exact ⟨rfl, rfl⟩
    exact ⟨p, h.exists.imp fun _ h => h.1, fun _ => h⟩
  choose p hp₀ hp using key
  have one : ∀ n, 0 < n → ∃ j, (p n).1 = (I j).ev n ∧ (p n).2 = (I j).ζ n := fun n hn => (hp n hn).exists
  have two : ∀ n m, 0 < n → 0 < m → ∃ j, ((p n).1 = (I j).ev n ∧ (p n).2 = (I j).ζ n) ∧
      (p (n * m)).1 = (I j).ev (n * m) ∧ (p (n * m)).2 = (I j).ζ (n * m) := fun n m hn hm =>
    ((hp n hn).and (hp _ (Nat.mul_pos hn hm))).exists
  refine ⟨{ ζ := fun n => (p n).2
            ev := fun n => (p n).1
            ζ_prim := fun n hn => ?_
            ζ_pow := fun n m hn hm => ?_
            add := fun n a b => ?_
            lin := fun n c a => ?_
            ker := fun n hn a => ?_
            onto := fun n hn x => ?_
            tower := fun n m hn hm a => ?_
            isom := fun n hn a b => ?_ }, fun M hM j₀ => ?_⟩
  · obtain ⟨j, -, h⟩ := one n hn
    rw [h]; exact (I j).ζ_prim n hn
  · obtain ⟨j, ⟨-, h⟩, -, h'⟩ := two n m hn hm
    rw [h, h']; exact (I j).ζ_pow n m hn hm
  · obtain ⟨j, h⟩ := hp₀ n
    rw [h]; exact (I j).add n a b
  · obtain ⟨j, h⟩ := hp₀ n
    rw [h]; exact (I j).lin n c a
  · obtain ⟨j, h⟩ := hp₀ n
    rw [h]; exact (I j).ker n hn a
  · obtain ⟨j, h⟩ := hp₀ n
    rw [h]; exact (I j).onto n hn x
  · obtain ⟨j, ⟨h, -⟩, h', -⟩ := two n m hn hm
    rw [h, h']; exact (I j).tower n m hn hm a
  · obtain ⟨j, h, h'⟩ := one n hn
    rw [h, h']; exact (I j).isom n hn a b
  · have h : ∀ᶠ j in (U : Filter ℕ), j₀ ≤ j := Nat.hyperfilter_le_atTop (Filter.eventually_ge_atTop j₀)
    exact (h.and (hp M hM)).exists

end GlobalTheory.Ex.TateLimit
