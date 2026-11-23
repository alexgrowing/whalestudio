import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLaw

open TopologicalSpace GlobalTheory.AmpleLocal

theorem gs_cst {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (D : X.Opens) (c : R)
    (z : X) (hz : z ∈ D) : gs (𝟙 X) z D (AbLaw.cst f D c) = gs (𝟙 X) z ⊤ (AbLaw.cst f ⊤ c) := by
  rw [← rs_cst f (le_top : D ≤ ⊤) c]
  exact gs_res (𝟙 X) z le_top hz _

theorem veryAmpleBy_pw : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X)
    (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ d : ℕ, 1 ≤ d →
    ∃ (n' : ℕ) (s' : Fin (n' + 1) → LB.Sec (pw H d)), VeryAmpleBy f (pw H d) s' := by
  intro R _ X f H n s hH ⟨cov, hs⟩ d hd
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  choose aff r hr surj using hs
  choose c hc using fun z : X => exists_chart hH z
  let G : H.ι → Fn X := fun i z => (gm (𝟙 X) z _ (H.g i (c z))).val
  let φ : R → Fn X := fun a z => gs (𝟙 X) z ⊤ (AbLaw.cst f ⊤ a)
  have hU : ∀ z, ∃ i, z ∈ H.U i := fun z => ⟨c z, hc z⟩
  have hG : ∀ i z, IsUnit (G i z) := fun _ _ => Units.isUnit _
  let σ : Fin (n + 1) → Fn X := fun i => sv c (s i)
  have hσ : ∀ i, Sc H.U G ⊤ 1 (σ i) := fun i =>
    sc_sv (P := H) (κ := id) (fun _ => le_rfl) hc (fun _ _ _ => (pow_one _).symm) (s i)
  have gen : ∀ i, Gen (nonzeroLocus (s i)) (Set.range φ ∪ Set.range fun m => σ m * AmpleLocal.inv (σ i)) := fun i =>
    (gen_iff _ (r i) _ _ (fun a z hz => gs_cst f _ a z hz)
      (fun m => (ratio_iff hc (s i) (s m) (r i m)).1 (hr i m))).2 (surj i)
  obtain ⟨M, hM⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_pos (α := Fin (n + 1) × Fin (n + 1))).ne'
  let ε := Fintype.equivFinOfCardEq hM
  let τ : Fin (M + 1) → Fn X := fun m => σ (ε.symm m).2 * σ (ε.symm m).1 ^ e
  have hτ : ∀ m, Sc H.U G ⊤ (1 * (e + 1)) (τ m) := fun m => by
    rw [mul_add, _root_.mul_one, add_comm]
    exact (hσ _).mul ((hσ _).pow _)
  have hγ : ∀ y, y ∈ (pw H ((e + 1 : ℕ) : ℤ)).U (c y) := hc
  choose t ht using fun m => exists_sv (P := pw H ((e + 1 : ℕ) : ℤ)) (κ := id) (N := 1 * (e + 1)) (G := G)
    (fun _ => le_rfl) hc (fun i y _ => by
      show (gm (𝟙 X) y _ (H.g i (c y) ^ ((e + 1 : ℕ) : ℤ))).val = _
      rw [zpow_natCast, map_pow, Units.val_pow_eq_pow_val, _root_.one_mul]) (isLB_pw hH _) (hτ m)
  have loc : ∀ m, IsLoc (nonzeroLocus (t m)) ⊤ (τ m) := fun m => ht m ▸ loc_sv hγ (t m)
  have main := fun m => extra_section hU hG hσ (fun i => loc_sv hc (s i))
    (fun z _ => Opens.mem_iSup.1 (cov.ge trivial)) aff (S₀ := Set.range φ)
    (by rintro _ ⟨a, rfl⟩; exact mem_reg_iff.2 ⟨_, fun _ _ => rfl⟩) gen (hτ m) (loc m)
  refine ⟨M, t, top_le_iff.1 fun z _ => ?_, fun i => ⟨(main i).1, ?_⟩⟩
  · obtain ⟨j, hj⟩ := Opens.mem_iSup.1 (cov.ge (Set.mem_univ z))
    have hu : IsUnit (σ j z) := (loc_sv hc (s j)).unit hj
    refine Opens.mem_iSup.2 ⟨ε (j, j), (loc _ z).2 ⟨trivial, ?_⟩⟩
    simp only [τ, Equiv.symm_apply_apply]
    exact hu.mul (hu.pow e)
  · choose ρ hρ using fun m => mem_reg_iff.1 (Sc.ratio hU hG (hτ m) (hτ i) (loc i))
    refine ⟨ρ, fun m => (ratio_iff hγ (t i) (t m) (ρ m)).2 ?_, ?_⟩
    · have e₁ : sv (P := pw H ((e + 1 : ℕ) : ℤ)) c (t i) = τ i := ht i
      have e₂ : sv (P := pw H ((e + 1 : ℕ) : ℤ)) c (t m) = τ m := ht m
      rw [e₁, e₂]
      exact hρ m
    · refine (gen_iff _ ρ φ _ (fun a z hz => gs_cst f _ a z hz) hρ).1 ((main i).2.mono ?_)
      rintro x (hx | ⟨p, rfl⟩)
      · exact ⟨x, Subring.subset_closure (Or.inl hx), fun _ _ => rfl⟩
      · refine ⟨_, Subring.subset_closure (Or.inr ⟨ε p, ?_⟩), fun _ _ => rfl⟩
        simp only [τ, Equiv.symm_apply_apply]

end GlobalTheory.AbLaw
