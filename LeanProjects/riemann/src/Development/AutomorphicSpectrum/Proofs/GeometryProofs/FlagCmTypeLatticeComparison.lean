import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsPullWedge
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ImaginaryRootConj
import Development.AutomorphicSpectrum.Statements.GeometryStatements.DivMemLineLat
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLatticeVectorBundle
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.WedgeLatticeGenerator
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.MemSpanOfIotaMultiProportional
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IotaMultiChangeOfBasisDet
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.CptWedge

section LinAlg

variable {Ω₀ Ω V₀ V : Type} [Field Ω₀] [Field Ω] [AddCommGroup V₀] [Module Ω₀ V₀] [AddCommGroup V] [Module Ω V]

theorem exists_wedge_eq_smul {n : ℕ} {e b : Fin n → V} (h : ∀ k, e k ∈ Submodule.span Ω (Set.range b)) :
    ∃ d : Ω, exteriorPower.ιMulti Ω n e = d • exteriorPower.ιMulti Ω n b := by
  choose T hT using fun k => (Submodule.mem_span_range_iff_exists_fun Ω).1 (h k)
  have he : e = fun k => ∑ l, (Matrix.of T) k l • b l := funext fun k => (hT k).symm
  exact ⟨(Matrix.of T).det, by rw [he]; exact GlobalTheory.CompanionTheory.Ar.Lat.wedge_matrix_mul_family Ω V n b _⟩

theorem isPullWedge_smul_ιMulti (i : Ω₀ →+* Ω) (j : V₀ →+ V) (hj : IsExtOver i j) {n : ℕ} {u : Fin n → V₀}
    (hu : LinearIndependent Ω₀ u) {γ : Ω₀} (hγ : γ ≠ 0) :
    CptIn.IsPullWedge i j (γ • exteriorPower.ιMulti Ω₀ n u)
      (i γ • exteriorPower.ιMulti Ω n fun k => j (u k)) := by
  intro b α hab
  have hw := WedgeFrame.ιMulti_ne_zero hu
  have hα : α ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hab
    exact smul_ne_zero hγ hw hab
  have hbe : exteriorPower.ιMulti Ω₀ n b = (α⁻¹ * γ) • exteriorPower.ιMulti Ω₀ n u := by
    rw [mul_smul, hab, smul_smul, inv_mul_cancel₀ hα, one_smul]
  have hm := GlobalTheory.CompanionTheory.WedgeSpan.span_of_wedge_proportional Ω₀ V₀ n b u _ hu (mul_ne_zero (inv_ne_zero hα) hγ) hbe
  choose T hT using fun k => (Submodule.mem_span_range_iff_exists_fun Ω₀).1 (hm k)
  have hb : b = fun k => ∑ l, (Matrix.of T) k l • u l := funext fun k => (hT k).symm
  have h1 : exteriorPower.ιMulti Ω₀ n b = (Matrix.of T).det • exteriorPower.ιMulti Ω₀ n u := by
    rw [hb]; exact GlobalTheory.CompanionTheory.Ar.Lat.wedge_matrix_mul_family Ω₀ V₀ n u _
  have h2 : γ = α * (Matrix.of T).det := by
    rw [h1, smul_smul] at hab
    exact smul_left_injective Ω₀ hw hab
  have h3 : (fun k => j (b k)) = fun k => ∑ l, (i.mapMatrix (Matrix.of T)) k l • j (u l) := by
    funext k
    rw [hb]
    simp only [map_sum, hj.1]
    rfl
  rw [h3, GlobalTheory.CompanionTheory.Ar.Lat.wedge_matrix_mul_family Ω V n _ _, ← RingHom.map_det, smul_smul, ← map_mul, ← h2]

end LinAlg

theorem exists_eq_smul_ιMulti {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type}
    [AddCommGroup E] [Module Ω E] {L : Lat ξ E} {r : ℕ} {u : Fin r → E} {x : Cpt ξ} (hu : L.IsFrameAt u x)
    {a : ⋀[Ω]^r E} {α : Ω} (hα : α ≠ 0) (hw : L.wedge r x = Submodule.span (regAt ξ x) {α • a}) :
    ∃ γ : Ω, γ ≠ 0 ∧ a = γ • exteriorPower.ιMulti Ω r u := by
  obtain ⟨h1, h2⟩ := WedgeFrame.wedge_eq_span_ιMulti X Ω ξ E L r u x hu
  have h3 : exteriorPower.ιMulti Ω r u ∈ Submodule.span (regAt ξ x) {α • a} := by
    rw [← hw, h1]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 h3
  have ht' : ((t : Ω) * α) • a = exteriorPower.ιMulti Ω r u := by
    rw [mul_smul]; exact ht
  have ht0 : (t : Ω) * α ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at ht'
    exact h2 ht'.symm
  exact ⟨((t : Ω) * α)⁻¹, inv_ne_zero ht0, by rw [← ht', smul_smul, inv_mul_cancel₀ ht0, one_smul]⟩

section Comparison₂

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {U : Set (Xo.XF c)} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type}
  {y : (Σ k, J k) → Ω}

theorem tie_act {Z : CptOver Y U} {𝔐 : HodgeCpt Y S y} {i : Z.Ω →+* Ω} {j : Z.V →+ 𝔐.Li}
    (h : CptIn.IsTie Z 𝔐 i j) (a : 𝓞 E) (e : Z.V) : j (Z.ρ a e) = 𝔐.ρ a (j e) := by
  obtain ⟨-, -, -, h4⟩ := h
  refine 𝔐.M.inj (Over.OverMorphism.ext (𝔐.m.cart.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm)))
  rw [h4, Z.act a e, 𝔐.act a (j e), Over.comp_left, Over.comp_left, Category.assoc, 𝔐.m.act, ← Category.assoc]
  exact (congrArg (· ≫ Over.Hom.left (Y.t.act.act a)) (h4 e).symm).trans (Category.assoc _ _ _)

theorem tie_mem_eigSp {Z : CptOver Y U} {𝔐 : HodgeCpt Y S y} {i : Z.Ω →+* Ω} {j : Z.V →+ 𝔐.Li}
    (h : CptIn.IsTie Z 𝔐 i j) (σ : 𝓞 E →+* c.F) {e : Z.V} (he : e ∈ eigSp Z.ρ (Z.inc.comp σ)) :
    j e ∈ eigSp 𝔐.ρ (𝔐.cst.comp σ) := by
  have hi := h.2.1
  have hs := h.2.2.1.1
  simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero] at he ⊢
  intro a
  rw [← tie_act h, he a, hs, ← hi]
  rfl

theorem exists_side {Z : CptOver Y U} {𝔐 : HodgeCpt Y S y} {i : Z.Ω →+* Ω} {j : Z.V →+ 𝔐.Li}
    (h : CptIn.IsTie Z 𝔐 i j) {L : Lat (Z.ξ₀ ≫ Y.j) Z.V} {r : ℕ} {u : Fin r → Z.V} {x : Cpt (Z.ξ₀ ≫ Y.j)}
    (hu : L.IsFrameAt u x) {a : ⋀[Z.Ω]^r Z.V} {α : Z.Ω} (hα : α ≠ 0)
    (hw : L.wedge r x = Submodule.span (regAt (Z.ξ₀ ≫ Y.j) x) {α • a}) {B : Fin r → 𝔐.Li}
    (hB : ∀ k, j (u k) ∈ Submodule.span Ω (Set.range B)) :
    ∃ (a' : ⋀[Ω]^r 𝔐.Li) (d : Ω), d ≠ 0 ∧ a' ≠ 0 ∧ CptIn.IsPullWedge i j a a' ∧
      a' = d • exteriorPower.ιMulti Ω r B := by
  obtain ⟨γ, hγ, rfl⟩ := exists_eq_smul_ιMulti hu hα hw
  have hj : IsExtOver i j := h.2.2.1
  have hind : LinearIndependent Ω fun k => j (u k) := hj.2 r u hu.1
  have hne := WedgeFrame.ιMulti_ne_zero hind
  obtain ⟨d, hd⟩ := exists_wedge_eq_smul hB
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hd
    exact hne hd
  have hiγ : i γ ≠ 0 := (map_ne_zero i).2 hγ
  exact ⟨_, i γ * d, mul_ne_zero hiγ hd0, smul_ne_zero hiγ hne, isPullWedge_smul_ιMulti i j hj hu.1 hγ,
    by rw [hd, smul_smul]⟩

end Comparison₂

theorem exists_pullWedge_flag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) [NumberField c.F] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (U : Set (Xo.XF c)) (Z : CptOver Y U) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (Fl : 𝔐.Flag) (τ : CMType H) (i : Z.Ω →+* Ω) (j : Z.V →+ 𝔐.Li) (a : ⋀[Z.Ω]^D.p Z.V) (b : ⋀[Z.Ω]^D.q Z.V), CptIn.IsTie Z 𝔐 i j → IsLineGenOn (Z.eig τ.1) (Z.eig (ComplexEmbedding.conjugate τ.1)) D.p D.q a b Z.genFib → ∃ (a' : ⋀[Ω]^D.p 𝔐.Li) (b' : ⋀[Ω]^D.q 𝔐.Li) (d₁ d₂ : Ω), d₁ ≠ 0 ∧ d₂ ≠ 0 ∧ a' ≠ 0 ∧ b' ≠ 0 ∧ CptIn.IsPullWedge i j a a' ∧ CptIn.IsPullWedge i j b b' ∧ a' = d₁ • (exteriorPower.ιMulti Ω _ (Fl.b (.inl τ))) ∧ b' = d₂ • (exteriorPower.ιMulti Ω _ (Fl.b (.inr τ))) := by
  intro E _ _ _ H D l Xo c _ Y U Z S Ω _ K _ J _ y 𝔐 Fl τ i j a b hT hL
  have hfr : ∀ x : c.F, ∃ a b : 𝓞 c.F, algebraMap (𝓞 c.F) c.F b ≠ 0 ∧
      x * algebraMap (𝓞 c.F) c.F b = algebraMap (𝓞 c.F) c.F a := by
    intro x
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 c.F)) x
    exact ⟨a, b, IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2, hab⟩
  obtain ⟨h1, h2, -, x, hx⟩ := isVBOn_eig_genFib E H D l Xo c (𝓞 c.F) (algebraMap (𝓞 c.F) c.F) Y U Z τ.1
    ⟨FaithfulSMul.algebraMap_injective _ _, inferInstance, hfr⟩ τ.2
  obtain ⟨-, -, hg⟩ := hL
  obtain ⟨α, β, hα, hβ, hwa, hwb, -⟩ := hg x hx
  obtain ⟨W₁, hW₁, u₁, hs₁, hf₁⟩ := h1 x hx
  obtain ⟨W₂, hW₂, u₂, hs₂, hf₂⟩ := h2 x hx
  have hu₁ := hf₁ x hx hW₁
  have hu₂ := hf₂ x hx hW₂
  have hB₁ : ∀ k, j (u₁ k) ∈ Submodule.span Ω (Set.range (Fl.b (.inl τ))) := fun k => by
    rw [HodgeCptTest.flag_span 𝔐 Fl]
    have hk : u₁ k ∈ eigSp Z.ρ (Z.inc.comp (tauIn c τ.1)) := hs₁ ▸ Submodule.subset_span ⟨k, rfl⟩
    have := tie_mem_eigSp hT _ hk
    rwa [← CptInputs.labelEmb_inl] at this
  have hB₂ : ∀ k, j (u₂ k) ∈ Submodule.span Ω (Set.range (Fl.b (.inr τ))) := fun k => by
    rw [HodgeCptTest.flag_span 𝔐 Fl]
    have hk : u₂ k ∈ eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ.1))) :=
      hs₂ ▸ Submodule.subset_span ⟨k, rfl⟩
    have := tie_mem_eigSp hT _ hk
    rwa [← CptInputs.labelEmb_inr] at this
  obtain ⟨a', d₁, hd₁, ha', hpa, hea⟩ := exists_side hT hu₁ hα hwa (B := Fl.b (.inl τ)) hB₁
  obtain ⟨b', d₂, hd₂, hb', hpb, heb⟩ := exists_side hT hu₂ hβ hwb (B := Fl.b (.inr τ)) hB₂
  exact ⟨a', b', d₁, d₂, hd₁, hd₂, ha', hb', hpa, hpb, hea, heb⟩

end GlobalTheory.CompanionTheory.Ar.Flat.CptWedge
