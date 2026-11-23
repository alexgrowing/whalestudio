import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CoefSup
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.QoExt
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem enat_cmp {a a' x x' : ℕ∞} (h : a' * x = a * x') (hx : x ≠ 0) (hx' : x' ≠ 0) (tx : x ≠ ⊤) (tx' : x' ≠ ⊤) :
    (a = ⊤ ↔ a' = ⊤) ∧ (a.toNat : ℝ) / (x.toNat : ℝ) = (a'.toNat : ℝ) / (x'.toNat : ℝ) := by
  lift x to ℕ using tx
  lift x' to ℕ using tx'
  have hx0 : (x : ℝ) ≠ 0 := by exact_mod_cast (fun h0 => hx (by simp [h0]))
  have hx0' : (x' : ℝ) ≠ 0 := by exact_mod_cast (fun h0 => hx' (by simp [h0]))
  induction a using ENat.recTopCoe with
  | top =>
    induction a' using ENat.recTopCoe with
    | top => simp
    | coe b =>
      exfalso
      rw [ENat.top_mul hx'] at h
      exact ENat.coe_ne_top _ (by exact_mod_cast h)
  | coe a =>
    induction a' using ENat.recTopCoe with
    | top =>
      exfalso
      rw [ENat.top_mul hx] at h
      exact ENat.coe_ne_top _ (by exact_mod_cast h.symm)
    | coe b =>
      have h' : b * x = a * x' := by exact_mod_cast h
      refine ⟨by simp, ?_⟩
      simp only [ENat.toNat_coe]
      rw [div_eq_div_iff hx0 hx0']
      exact_mod_cast h'.symm

private theorem eO_ne {l : ℕ} [Fact l.Prime] (c : Coef l) : eO l c.O ≠ 0 ∧ eO l c.O ≠ ⊤ := by
  obtain ⟨-, -, -, -, -, h0, hle, -⟩ := dvrFacts l c.O
  exact ⟨h0, ne_top_of_le_ne_top (ENat.coe_ne_top _) hle⟩

private theorem coef_le (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c c' : Coef l)
    (hle : c.O ≤ c'.O) (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (ψ' : DirichletCharacter c'.O N)
    (hψ : ∀ a : ZMod N, ((ψ a : c.O) : PadicAlgCl l) = ((ψ' a : c'.O) : PadicAlgCl l)) :
    (Vlen Ω c e ψ = ⊤ ↔ Vlen Ω c' e ψ' = ⊤) ∧ Vn Ω c e ψ = Vn Ω c' e ψ' := by
  haveI := c.dvr
  haveI := c'.dvr
  haveI := c.fin
  haveI := c'.fin
  letI : Algebra c.O c'.O := (Subalgebra.inclusion hle).toRingHom.toAlgebra
  haveI : IsScalarTower ℤ_[l] c.O c'.O := IsScalarTower.of_algebraMap_eq (fun x => Subtype.ext rfl)
  have hcoe : ∀ y : c.O, ((algebraMap c.O c'.O y : c'.O) : PadicAlgCl l) = (y : PadicAlgCl l) := fun y => rfl
  set θ : Formalism.ConjugateSelfDual.G ℚ Ω →* c.O ˣ := (Chr.dirG ℚ Ω ψ)⁻¹ * chiO ℚ Ω l c.O ^ (-(e : ℤ)) with hθ
  obtain ⟨hq, -⟩ := qoExt l (Formalism.ConjugateSelfDual.G ℚ Ω) c.O c'.O θ ⊤ (shaFam ℚ Ω (l * N))
  have hmap : (Units.map (algebraMap c.O c'.O : c.O →* c'.O)).comp θ
      = (Chr.dirG ℚ Ω ψ')⁻¹ * chiO ℚ Ω l c'.O ^ (-(e : ℤ)) := by
    ext g
    have h1 : (Units.map (algebraMap c.O c'.O : c.O →* c'.O)) (Chr.dirG ℚ Ω ψ g) = Chr.dirG ℚ Ω ψ' g := by
      apply Units.ext
      apply Subtype.ext
      simp only [Units.coe_map, MonoidHom.coe_coe, hcoe]
      exact hψ _
    have h2 : (Units.map (algebraMap c.O c'.O : c.O →* c'.O)) (chiO ℚ Ω l c.O g) = chiO ℚ Ω l c'.O g := by
      apply Units.ext
      simp only [chiO, Units.coe_map, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_coe]
      exact (IsScalarTower.algebraMap_apply ℤ_[l] c.O c'.O _).symm
    simp only [hθ, MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.zpow_apply, map_mul, map_inv, map_zpow, h1, h2]
  erw [hmap] at hq
  exact enat_cmp hq (eO_ne c).1 (eO_ne c').1 (eO_ne c).2 (eO_ne c').2

theorem UpperTheory.V.HV.coefIndep :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (c c' : Coef l) (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N) (ψ' : DirichletCharacter c'.O N),
      (∀ a : ZMod N, ((ψ a : c.O) : PadicAlgCl l) = ((ψ' a : c'.O) : PadicAlgCl l)) →
      (Vlen Ω c e ψ = ⊤ ↔ Vlen Ω c' e ψ' = ⊤) ∧ Vn Ω c e ψ = Vn Ω c' e ψ' := by
  intro Ω _ _ _ l _ c c' N _ e ψ ψ' h
  obtain ⟨c'', h1, h2⟩ := (coefSup l).1 c c'
  let ψ'' : DirichletCharacter c''.O N := ψ.ringHomComp (Subalgebra.inclusion h1).toRingHom
  obtain ⟨a1, b1⟩ := coef_le Ω l c c'' h1 N e ψ ψ'' fun _ => rfl
  obtain ⟨a2, b2⟩ := coef_le Ω l c' c'' h2 N e ψ' ψ'' fun a => (h a).symm
  exact ⟨a1.trans a2.symm, b1.trans b2.symm⟩
