import Development.AutomorphicArithmetic.LocalEmbeddings.RootFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalModelOverProjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.RootFrame

private theorem exists_cover {F : Type} [Field F] [NumberField F] (Y : Var F) {N : ℕ} (M : Fin N → GlobalTheory.TrueGeo.Model Y) :
    ∃ (V : Cover Y) (b : ∀ i, V.X ⟶ (M i).X), ∀ i, V.j ≫ b i = V.π ≫ (M i).j := by
  obtain ⟨X', π, j, hXi, hπ, hfl, H, hg⟩ := GlobalTheory.IntModel.exists_flat_model (O := 𝓞 F) Y.str Y.isProjOver
    (fun i => (M i).X) (fun i => (M i).p) (fun i => (M i).j) (fun i => (M i).ar.isProjOver) (fun i => (M i).pb.w)
  have := CommonModel.isProper_of_isProjOver hπ
  have hZ : Flat (spMap (Int.castRingHom (𝓞 F))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact (RingHom.flat_algebraMap_iff (R := ℤ) (S := 𝓞 F)).2 inferInstance
  have har : IsArithVar π Y.dim := ⟨inferInstance, inferInstance, hXi, hπ, inferInstance,
    GlobalTheory.IntModel.topologicalKrullDim_eq_succ (RingOfIntegers.not_isField F) H Y.topologicalKrullDim_eq⟩
  let M₀ : GlobalTheory.TrueGeo.Model Y := ⟨X', π, har, j, H⟩
  obtain ⟨Q, π₁, -, hQ, -, -, hj, -⟩ := GlobalTheory.ModelDom.exists_normal_dominating F Y M₀ M₀
  choose g hg₁ _ using hg
  refine ⟨Cover.ofModel Q hQ, fun i => π₁ ≫ g i, fun i => ?_⟩
  show Q.j ≫ π₁ ≫ g i = 𝟙 _ ≫ (M i).j
  rw [← Category.assoc, hj, Category.id_comp]
  exact hg₁ i

theorem UpperTheory.exists_cover_power_readings :
    ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (N : ℕ) (Δ : Fin N → Y.Dv) (φ : Fin N → PtFn Y), (∀ i, FromModel Y (Δ i) (eqn (Δ i)) (φ i)) → ∃ V₀ : Cover Y, ∀ (V : Cover Y) (a : V.X ⟶ V₀.X) (g : V.G ⟶ V₀.G), V.j ≫ a = g ≫ V₀.j → g ≫ V₀.π = V.π → ∀ (p : ℕ) (i : Fin N), PowRead V p (genAt (Δ i)) (φ i) := by
  intro F _ _ Y N Δ φ h
  choose M L m r hL hr hv using h
  obtain ⟨V₀, b, hb⟩ := exists_cover Y M
  refine ⟨V₀, fun V a g hj hπ p i => ⟨m i, (m i).2, fun x _ => ?_⟩⟩
  have hc : V.j ≫ a ≫ b i = V.π ≫ (M i).j := by
    rw [← Category.assoc, hj, Category.assoc, hb, ← Category.assoc, hπ]
  obtain ⟨i₀, hi₀⟩ := exists_chart (hL i) ((a ≫ b i) x)
  have hu : ∀ z : V.G, V.j z ∈ (a ≫ b i) ⁻¹ᵁ (L i).U i₀ →
      UnitAt (V.π z) (genAt (Δ i) (V.π z) ^ (m i : ℕ) * (r i (fun _ => i₀) : Y.Fn)) := by
    intro z hz
    have hg : ((m i : ℕ) • Δ i).GeneratesAt (V.π z) (genAt (Δ i) (V.π z) ^ (m i : ℕ)) := by
      have := CartierDiv.isEqn_iff_generatesAt_inv.1 ((Base.isEqn_eqn (Δ i) (V.π z)).nsmul (m i))
      rwa [Units.val_pow_eq_pow_val, ← inv_pow, ← Units.val_inv_eq_inv_val] at this
    refine ((hr i).isEqn (fun _ => i₀) _ ?_).generatesAt_iff.1 hg
    refine Set.mem_iInter.2 fun _ => ?_
    show (V.π ≫ (M i).j) z ∈ (L i).U i₀
    rw [← hc]
    exact hz
  refine ⟨(a ≫ b i) ⁻¹ᵁ (L i).U i₀, V.φ (r i (fun _ => i₀)), hi₀, fun z hz => ?_, ?_⟩
  · rw [← map_pow, ← map_mul]
    exact V.unitAt_φ (hu z hz)
  · rintro v e y z yt ⟨-, -, e₁, e₂⟩ hi
    have hz : V.j (below z) ∈ (a ≫ b i) ⁻¹ᵁ (L i).U i₀ := by
      show (z ≫ V.j) (IsLocalRing.closedPoint _) ∈ _
      rw [← e₂]
      exact hi (Set.mem_univ _)
    have hU := hu _ hz
    have hπz : V.π (below z) = below y.1 := by
      rw [← e₁]
      rfl
    have H := hv i v e y (yt ≫ a ≫ b i) (fun _ => i₀)
      (by rw [← Category.assoc, e₂, Category.assoc, hc, ← Category.assoc, e₁]) hi
    rw [← hπz, ← map_pow, ← map_mul, V.valAt_φ z hU.regAt, e₁, hπz, H, Units.val_mul, Units.val_pow_eq_pow_val]
