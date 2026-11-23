import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CocycleTraceZero
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BaseRepGL3NormalisedOfPsiEqOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IrreducibleSpans.Burnside

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg GlobalTheory.GalOfCusp

private theorem detG_central {K G : Type} [Field K] [Group G] {n : ℕ}
    (m : G →* Matrix (Fin n) (Fin n) K) (χ : G →* Kˣ) (N : Subgroup G)
    (w : G → Matrix (Fin n) (Fin n) K) (hc : commutator G ≤ N) (hk : N ≤ χ.ker) (hχ : χ ≠ 1)
    (hspan : Submodule.span K (Set.range (m.comp N.subtype)) = ⊤)
    (hw : ∀ g g', w (g * g') = w g + (χ g : K) • (m g * w g' * m g⁻¹))
    (h0 : ∀ g ∈ N, w g = 0) :
    ∃ A, ∀ g, w g = (χ g : K) • (m g * A * m g⁻¹) - A := by
  have hinv : ∀ g, m g⁻¹ * m g = 1 := fun g => by rw [← map_mul, inv_mul_cancel, map_one]
  have hinv' : ∀ g, m g * m g⁻¹ = 1 := fun g => by rw [← map_mul, mul_inv_cancel, map_one]
  have hcom : ∀ g h : G, g * h * g⁻¹ * h⁻¹ ∈ N := fun g h =>
    hc (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top h))
  have hone : ∀ x ∈ N, (χ x : K) = 1 := fun x hx => by
    have : χ x = 1 := hk hx
    rw [this, Units.val_one]
  have hconj : ∀ g, ∀ x ∈ N, w g = m x * w g * m x⁻¹ := by
    intro g x hx
    have hy : g⁻¹ * x * g ∈ N := by
      have := N.mul_mem (hcom g⁻¹ x) hx
      simpa [mul_assoc] using this
    have e : x * g = g * (g⁻¹ * x * g) := by simp [mul_assoc]
    have h1 := hw x g
    rw [e, hw, h0 _ hy, h0 _ hx, hone x hx] at h1
    simpa using h1
  have hcen : ∀ g (X : Matrix (Fin n) (Fin n) K), X * w g = w g * X := by
    intro g X
    have hX : X ∈ Submodule.span K (Set.range (m.comp N.subtype)) := hspan ▸ Submodule.mem_top
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, rfl⟩ := hx
      change m y * w g = w g * m y
      conv_rhs => rw [hconj g y y.2]
      rw [mul_assoc, hinv, mul_one]
    | zero => simp
    | add x y _ _ h₁ h₂ => rw [mul_add, add_mul, h₁, h₂]
    | smul a x _ h₁ => rw [mul_smul_comm, smul_mul_assoc, h₁]
  have hfix : ∀ g h, m g * w h * m g⁻¹ = w h := fun g h => by
    rw [hcen, mul_assoc, hinv', mul_one]
  have hw' : ∀ g h, w (g * h) = w g + (χ g : K) • w h := fun g h => by rw [hw, hfix]
  have hsym : ∀ g h, w (g * h) = w (h * g) := by
    intro g h
    have e : g * h = (g * h * g⁻¹ * h⁻¹) * (h * g) := by simp [mul_assoc]
    rw [e, hw' (g * h * g⁻¹ * h⁻¹), h0 _ (hcom g h), hone _ (hcom g h), zero_add, one_smul]
  obtain ⟨h, hh⟩ : ∃ h, χ h ≠ 1 := by
    by_contra hn
    exact hχ (MonoidHom.ext fun g => by_contra fun hg => hn ⟨g, hg⟩)
  have hh' : (χ h : K) - 1 ≠ 0 := fun e => hh (Units.ext (by simpa using sub_eq_zero.mp e))
  refine ⟨((χ h : K) - 1)⁻¹ • w h, fun g => ?_⟩
  have h1 := hsym g h
  rw [hw', hw'] at h1
  have h2 : ((χ h : K) - 1) • w g = (χ g : K) • w h - w h := by
    rw [sub_smul, one_smul, sub_eq_sub_iff_add_eq_add, add_comm, ← h1, add_comm]
  rw [mul_smul_comm, smul_mul_assoc, hfix, smul_comm, ← smul_sub, ← h2, smul_smul,
    inv_mul_cancel₀ hh', one_smul]

theorem UpperTheory.V.Th.Det.detG :
    ∀ {K G : Type} [Field K] [IsAlgClosed K] [Group G] {n : ℕ} (ρ : G →* GL (Fin n) K) (χ : G →* Kˣ) (N : Subgroup G) (z : G → Matrix (Fin n) (Fin n) K), 1 ≤ n → commutator G ≤ N → N ≤ χ.ker → χ ≠ 1 → U3.MatIrr N (W.mat ρ) → (∀ g g', z (g * g') = z g + (χ g : K) • (W.mat ρ g * z g' * W.mat ρ g⁻¹)) → (∀ g ∈ N, (z g * W.mat ρ g).trace = 0) → ∃ Y, ∀ g, z g = (χ g : K) • (W.mat ρ g * Y * W.mat ρ g⁻¹) - Y := by
  intro K G _ _ _ n ρ χ N z hn hc hk hχ hirr hz htr
  generalize W.mat ρ = m at hirr hz htr ⊢
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hone : ∀ x ∈ N, (χ x : K) = 1 := fun x hx => by
    have : χ x = 1 := hk hx
    rw [this, Units.val_one]
  have hspan : Submodule.span K (Set.range (m.comp N.subtype)) = ⊤ :=
    KStar.Schema.span_eq_top_of_irreducible _ fun U hU => hirr U fun g hg v hv => hU ⟨g, hg⟩ v hv
  let r : N →* (∀ _ : Unit, Matrix (Fin n) (Fin n) K) := MonoidHom.pi fun _ => m.comp N.subtype
  have hspan' : Submodule.span K (Set.range r) = ⊤ := by
    let L : Matrix (Fin n) (Fin n) K →ₗ[K] (∀ _ : Unit, Matrix (Fin n) (Fin n) K) :=
      LinearMap.pi fun _ => LinearMap.id
    have hL : Function.Surjective L := fun x => ⟨x (), rfl⟩
    have e : Set.range r = L '' Set.range (m.comp N.subtype) := by
      rw [← Set.range_comp]; rfl
    rw [e, ← Submodule.map_span, hspan, Submodule.map_top, LinearMap.range_eq_top.mpr hL]
  obtain ⟨Y₀, hY₀⟩ := UpperTheory.V.AlgebraTools.cocycle_trace_zero (K := K) (fun _ : Unit => Fin n) r
    (fun g _ => z g) hspan'
    (fun g h => by
      funext s
      have := hz g h
      rw [hone g g.2, one_smul] at this
      exact this)
    (fun g => by
      rw [Fintype.sum_unique]
      exact htr g g.2)
  have hY : ∀ g ∈ N, z g = Y₀ () - m g * Y₀ () * m g⁻¹ := fun g hg => congrFun (hY₀ ⟨g, hg⟩) ()
  have hinv' : ∀ g, m g * m g⁻¹ = 1 := fun g => by rw [← map_mul, mul_inv_cancel, map_one]
  obtain ⟨A, hA⟩ := detG_central m χ N
    (fun g => z g + ((χ g : K) • (m g * Y₀ () * m g⁻¹) - Y₀ ())) hc hk hχ hspan
    (fun g h => by
      simp only [hz, map_mul, _root_.mul_inv_rev, Units.val_mul, mul_add, add_mul, mul_sub, sub_mul,
        smul_add, smul_sub, mul_smul_comm, smul_mul_assoc, smul_smul, mul_assoc]
      abel)
    (fun g hg => by
      simp only [hY g hg, hone g hg, one_smul]
      abel)
  refine ⟨A - Y₀ (), fun g => ?_⟩
  have := hA g
  simp only [mul_sub, sub_mul, smul_sub]
  rw [eq_sub_of_add_eq this]
  abel
