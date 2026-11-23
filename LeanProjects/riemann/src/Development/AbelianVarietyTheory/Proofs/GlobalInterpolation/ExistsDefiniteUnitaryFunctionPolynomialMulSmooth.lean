import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DefiniteUnitaryRealApproxAndFiniteInfiniteSplitStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryCoordinateAlgebraDenseStatement

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC

namespace GlobalTheory.UnitaryBC

theorem continuous_of_right_invariant_open {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (e : G → ℂ) (V : Subgroup G) (hV : IsOpen (V : Set G)) (h : ∀ u ∈ V, ∀ g, e (g * u) = e g) :
    Continuous e := by
  refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_exists_open e).2 fun x => ?_)
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (V : Set G), hV.preimage (by fun_prop), by simp, fun y hy => ?_⟩
  rw [← h _ hy x, mul_inv_cancel_left]

theorem exists_fun_of_poly_smooth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (m : ℕ) (p : Fin m → infU E n → ℂ) (e : Fin m → finU E n → ℂ), (∀ i, p i ∈ Algebra.adjoin ℂ {f : infU E n → ℂ | ∃ (τ : E →+* ℂ) (i j : Fin n), f = fun x => (cEmb τ x.1).val i j}) → (∀ i, ∃ V : Subgroup (finU E n), IsOpen (V : Set (finU E n)) ∧ ∀ u ∈ V, ∀ g, e i (g * u) = e i g) → ∃ φ : UA E n → ℂ, Continuous φ ∧ IsOpen {k : finU E n | RU E n k φ = φ} ∧ FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : infU E n => RU E n k φ)) ∧ ∀ (g : finU E n) (k : infU E n), φ (g.1 * k.1) = ∑ i, p i k * e i g := by
  intro E _ _ _ n m p e hp he
  obtain ⟨-, -, -, a, b, ha, hb, -, hab⟩ := GlobalTheory.T.definiteUnitary_realApprox_and_finite_infinite_split E n
  obtain ⟨hcont, -, -, -, hco⟩ := GlobalTheory.T.unitary_coordinate_algebra_dense E n
  choose V hVo hV using he
  have haf : ∀ g : finU E n, a g.1 = g := fun g => by simpa using (hab g 1).1
  have hbf : ∀ g : finU E n, b g.1 = 1 := fun g => by simpa using (hab g 1).2
  have hai : ∀ k : infU E n, a k.1 = 1 := fun k => by simpa using (hab 1 k).1
  have hbi : ∀ k : infU E n, b k.1 = k := fun k => by simpa using (hab 1 k).2
  have hR : ∀ (x : UA E n) (φ : UA E n → ℂ) (g : UA E n), RU E n x φ g = φ (g * x) := fun _ _ _ => rfl
  refine ⟨fun x => ∑ i, p i (b x) * e i (a x), ?_, ?_, ?_, fun g k => ?_⟩
  · exact continuous_finsetSum _ fun i _ => ((hcont _ (hp i)).comp hb).mul
      ((continuous_of_right_invariant_open _ _ (hVo i) (hV i)).comp ha)
  · set φ : UA E n → ℂ := fun x => ∑ i, p i (b x) * e i (a x) with hφ
    let S : Subgroup (finU E n) :=
      { carrier := {k : finU E n | RU E n k φ = φ}
        one_mem' := by
          change RU E n ((1 : finU E n) : UA E n) φ = φ
          funext g
          rw [hR]
          simp
        mul_mem' := fun {x y} hx hy => by
          change RU E n ((x * y : finU E n) : UA E n) φ = φ
          funext g
          have h1 := congrFun (show RU E n x φ = φ from hx) g
          have h2 := congrFun (show RU E n y φ = φ from hy) (g * x)
          rw [hR] at h1 h2 ⊢
          rw [Subgroup.coe_mul, ← mul_assoc, h2, h1]
        inv_mem' := fun {x} hx => by
          change RU E n ((x⁻¹ : finU E n) : UA E n) φ = φ
          funext g
          have h1 := congrFun (show RU E n x φ = φ from hx) (g * (x : UA E n)⁻¹)
          rw [hR] at h1 ⊢
          rw [Subgroup.coe_inv, ← h1, inv_mul_cancel_right] }
    have hle : (⨅ i, V i) ≤ S := fun u hu => by
      change RU E n (u : UA E n) φ = φ
      funext g
      rw [hR]
      simp only [hφ, map_mul, haf, hbf, mul_one]
      exact Finset.sum_congr rfl fun i _ => by rw [hV i u (Subgroup.mem_iInf.1 hu i)]
    refine Subgroup.isOpen_mono hle ?_
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite hVo
  · choose N c d _ hcd using fun i => hco _ (hp i)
    let f : (Σ i, Fin (N i)) → UA E n → ℂ := fun s x => c s.1 s.2 (b x) * e s.1 (a x)
    haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range f)) :=
      FiniteDimensional.span_of_finite ℂ (Set.finite_range f)
    refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ (Set.range f)) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    have : RU E n k (fun x => ∑ i, p i (b x) * e i (a x)) = ∑ s : Σ i, Fin (N i), d s.1 s.2 k • f s := by
      funext g
      rw [hR]
      simp only [map_mul, hai, hbi, mul_one, hcd, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, f,
        Fintype.sum_sigma, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    change RU E n k _ ∈ _
    rw [this]
    exact Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨s, rfl⟩)
  · simp only [(hab g k).1, (hab g k).2]

end GlobalTheory.UnitaryBC
