import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantHeatOperatorActsOnFourierTermsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeatOperatorValueAtPointEqRingOperatorStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGeneratingFramesComplete
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesGeneratingAtPoint
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsDivOfExpandsAt
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionOfIntegralSectionIsIntegral
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConstantCoeffDmonOfProdLinear
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LogDerivativePrincipalPolarisationIndependent
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpansionTranslateTorus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeatValues

theorem ringOp_mem {Ω : Type} [CommRing Ω] (J : Ideal Ω) {n : ℕ} (d : Derivation ℤ Ω Ω)
    (δ : Fin n → Derivation ℤ Ω Ω) (Θ : Matrix (Fin n) (Fin n) Ω) (u : Fin n → Ω) (p p' : Ω) (k : ℕ)
    (N : ℕ) (y : Ω) (hy : y ∈ J ^ (N + 2)) :
    ringOp ⇑d (fun a => ⇑(δ a)) Θ u p p' k y ∈ J ^ N := by
  have h1 : ∀ (D : Derivation ℤ Ω Ω) (x : Ω), x ∈ J ^ (N + 1 + 1) → D x ∈ J ^ (N + 1) := fun D x hx =>
    GlobalTheory.SymbolOne.deriv_mem_pow D J (N + 1) x hx
  have h2 : ∀ (D : Derivation ℤ Ω Ω) (x : Ω), x ∈ J ^ (N + 1) → D x ∈ J ^ N := fun D x hx =>
    GlobalTheory.SymbolOne.deriv_mem_pow D J N x hx
  have le1 : J ^ (N + 1) ≤ J ^ N := Ideal.pow_le_pow_right (Nat.le_succ N)
  have le2 : J ^ (N + 2) ≤ J ^ N := Ideal.pow_le_pow_right (by omega)
  unfold ringOp
  refine add_mem (add_mem (sub_mem ?_ ?_) ?_) ?_
  · exact Ideal.mul_mem_left _ _ (le1 (h1 d y hy))
  · exact Ideal.sum_mem _ fun a _ => Ideal.sum_mem _ fun b _ => Ideal.mul_mem_left _ _ (h2 _ _ (h1 _ _ hy))
  · exact Ideal.mul_mem_left _ _ (Ideal.sum_mem _ fun a _ => Ideal.mul_mem_left _ _ (le1 (h1 _ _ hy)))
  · exact Ideal.mul_mem_left _ _ (le2 hy)

theorem ringOp_add {Ω : Type} [CommRing Ω] {n : ℕ} (d : Derivation ℤ Ω Ω)
    (δ : Fin n → Derivation ℤ Ω Ω) (Θ : Matrix (Fin n) (Fin n) Ω) (u : Fin n → Ω) (p p' : Ω) (k : ℕ) (f g : Ω) :
    ringOp ⇑d (fun a => ⇑(δ a)) Θ u p p' k (f + g) =
      ringOp ⇑d (fun a => ⇑(δ a)) Θ u p p' k f + ringOp ⇑d (fun a => ⇑(δ a)) Θ u p p' k g := by
  unfold ringOp
  simp only [map_add, mul_add, Finset.sum_add_distrib]
  ring

theorem ringOp_mul {Ω : Type} [CommRing Ω] {n : ℕ} (d : Derivation ℤ Ω Ω)
    (δ : Fin n → Derivation ℤ Ω Ω) (Θ : Matrix (Fin n) (Fin n) Ω) (u : Fin n → Ω) (p p' : Ω) (k : ℕ) (c f : Ω)
    (hc : ∀ a, δ a c = 0) :
    ringOp ⇑d (fun a => ⇑(δ a)) Θ u p p' k (c * f) =
      c * ringOp ⇑d (fun a => ⇑(δ a)) Θ u p p' k f + 2 * (k : Ω) * d c * f := by
  have e1 : ∀ a x, δ a (c * x) = c * δ a x := fun a x => by
    rw [Derivation.leibniz, hc, smul_zero, add_zero, smul_eq_mul]
  have e2 : ∀ a b, Θ a b * δ a (δ b (c * f)) = c * (Θ a b * δ a (δ b f)) := fun a b => by
    rw [e1, e1]; ring
  have e3 : ∀ a, u a * δ a (c * f) = c * (u a * δ a f) := fun a => by rw [e1]; ring
  have e4 : d (c * f) = c * d f + f * d c := by rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  unfold ringOp
  simp only [e2, e3, ← Finset.mul_sum, e4]
  ring

theorem eq_of_adic {Ω Idx : Type} [CommRing Ω] (J : Ideal Ω) [IsHausdorff J Ω] (T : Ω →+ Ω)
    (hT : ∀ N y, y ∈ J ^ (N + 2) → T y ∈ J ^ N) (c s s' : Ω) (t t' : Idx → Ω)
    (ht : ∀ α, t' α = c * T (t α))
    (hs : ∀ e : ℕ, ∃ S : Finset Idx, (∀ α ∉ S, t α ∈ J ^ (e + 1)) ∧ s - ∑ α ∈ S, t α ∈ J ^ (e + 1))
    (hs' : ∀ e : ℕ, ∃ S : Finset Idx, (∀ α ∉ S, t' α ∈ J ^ (e + 1)) ∧ s' - ∑ α ∈ S, t' α ∈ J ^ (e + 1)) :
    s' = c * T s := by
  classical
  rw [← sub_eq_zero]
  refine IsHausdorff.haus' (I := J) _ fun N => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  obtain ⟨S, hS1, hS2⟩ := hs (N + 1)
  obtain ⟨S', hS1', hS2'⟩ := hs' (N + 1)
  have split : ∀ (v : Idx → Ω) (A B : Finset Idx), ∑ α ∈ A ∪ B, v α = ∑ α ∈ A, v α + ∑ α ∈ B \ A, v α := by
    intro v A B
    rw [← Finset.union_sdiff_self_eq_union, Finset.sum_union Finset.disjoint_sdiff]
  have m1 : s - ∑ α ∈ S ∪ S', t α ∈ J ^ (N + 2) := by
    rw [split, sub_add_eq_sub_sub]
    exact sub_mem hS2 (Ideal.sum_mem _ fun α hα => hS1 α (Finset.mem_sdiff.1 hα).2)
  have m2 : s' - ∑ α ∈ S ∪ S', t' α ∈ J ^ (N + 2) := by
    rw [Finset.union_comm, split, sub_add_eq_sub_sub]
    exact sub_mem hS2' (Ideal.sum_mem _ fun α hα => hS1' α (Finset.mem_sdiff.1 hα).2)
  have e : s' - c * T s = (s' - ∑ α ∈ S ∪ S', t' α) + c * T (-(s - ∑ α ∈ S ∪ S', t α)) := by
    simp only [ht, ← Finset.mul_sum, ← map_sum, map_neg, map_sub]
    ring
  rw [e]
  exact add_mem (Ideal.pow_le_pow_right (by omega) m2)
    (Ideal.mul_mem_left _ _ (hT N _ (neg_mem m1)))

end GlobalTheory.HeatValues

namespace GlobalTheory.HeatValues

theorem gs_id_eq {Ω : Type} [CommRing Ω] (z : Sp Ω) (a : Ω) :
    gs (𝟙 (Sp Ω)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom a) = toStkA z a := by
  rw [gs_eq (𝟙 (Sp Ω)) z ⊤ (show (𝟙 (Sp Ω) : Sp Ω ⟶ Sp Ω) z ∈ (⊤ : (Sp Ω).Opens) from trivial)]
  rfl

theorem cst_id {Ω : Type} [CommRing Ω] (z : Sp Ω) (a : Ω) : cst (𝟙 (Sp Ω)) z a = toStkA z a :=
  gs_id_eq z a

noncomputable def cstR {A : Type} [CommRing A] {Z : Scheme.{0}} (q : Z ⟶ Sp A) (z : Z) : A →+* Z.presheaf.stalk z where
  toFun a := cst q z a
  map_one' := by simp only [cst, map_one, gs_eq q z ⊤ (show q z ∈ (⊤ : (Sp A).Opens) from trivial)]
  map_mul' a b := by simp only [cst, map_mul, gs_mul q z ⊤ (show q z ∈ (⊤ : (Sp A).Opens) from trivial)]
  map_zero' := by simp only [cst, map_zero, gs_eq q z ⊤ (show q z ∈ (⊤ : (Sp A).Opens) from trivial)]
  map_add' a b := by simp only [cst, map_add, gs_add q z ⊤ (show q z ∈ (⊤ : (Sp A).Opens) from trivial)]

theorem cstR_id {Ω : Type} [CommRing Ω] (z : Sp Ω) (a : Ω) : cstR (𝟙 (Sp Ω)) z a = toStkA z a :=
  gs_id_eq z a

theorem sval_secAdd {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s t : (LB.LinComb L φ ε).Sec) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (DVR.SecOps.secAdd s t) r z J = sval s r z J + sval t r z J :=
  gs_add r z _ (hJ.mem φ r) _ _

theorem exists_integral {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (U : Unif I D A G) (k : ℕ) (hk : 1 ≤ k) (σ : H0 U.LG.L k) :
    ∃ (r₀ : R) (σ₀ : H0 U.LG.L k) (f₀ : ∀ α, D.toPre.SecB k α) (F : Fam D.toPre (FractionRing R) k),
      r₀ ≠ 0 ∧ DVR.SecIsMul G.hom r₀ σ₀ σ ∧ (∀ e, U.ExpandsAt e k σ₀ f₀) ∧
      ∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) (F.s α)
        (D.toPre.famφB α) (DegPre.famε k) (f₀ α) (DegPre.prB D.toPre (FractionRing R)).left
        (scal (DegPre.BF D.toPre (FractionRing R)).hom r₀) := by
  have := U.smooth
  have : Flat G.hom := inferInstance
  have hL := U.LG.isLB
  obtain ⟨s, hs⟩ := exists_sec hL (φ := fun _ : Fin 1 => pullback.fst G.hom (jK R) ≫ 𝟙 G.left)
    (ε := fun _ => (k : ℤ)) (φ' := fun _ : Fin 1 => pullback.fst G.hom (jK R)) (ε' := fun _ => (k : ℤ))
    (fun _ _ _ => by simp only [Category.comp_id])
    (DVR.pullSec U.LG.L _ _ σ (pullback.fst G.hom (jK R)))
  obtain ⟨F, ⟨r₀, hr₀, σ₀, f₀, h₁, hf₁, hE⟩, -⟩ := (U.expand k hk).1 s
  have hσs : GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => (k : ℤ)) s
      (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) σ (pullback.fst G.hom (jK R)) 1 :=
    DVR.SectionScalarValuation.secScal_of_sval hL fun y J hJ => by
      rw [hs _ _ y J hJ, DVR.SectionScalarValuation.sval_pullSec _ _ σ _ _ y hJ]
  exact ⟨r₀, σ₀, f₀, F, hr₀, GlobalTheory.ExpInt.secIsMul_of_generic G hL k σ σ₀ s r₀ hσs h₁, hE, hf₁⟩

theorem shiftEq_of_fam {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) (k : ℕ)
    (F : Fam Q (FractionRing R) k) (f : ∀ α, Q.SecB k α) (r₀ : R)
    (hf : ∀ α, GeneratorPullback.SecScal Q.P.L (DegPre.famφ Q (FractionRing R) α) (DegPre.famε k) (F.s α)
      (Q.famφB α) (DegPre.famε k) (f α) (DegPre.prB Q (FractionRing R)).left
      (scal (DegPre.BF Q (FractionRing R)).hom r₀)) (mu α : Q.X) :
    ShiftEq Q k mu α (f α) (f (α + k • mu)) 0 (f (α + k • mu)) := by
  intro u hu hc z J hJ
  have fe := (secRel_iff Q.P.isLB _ _ _ _ _ _ _ _ _ u).1 (F.fe mu α u hu hc) _ (𝟙 _) z J hJ
  have a1 := GlobalTheory.IntegralExpansion.sval_of_secScal (hf (α + k • mu)) (𝟙 _) z hJ
  have a2 := GlobalTheory.IntegralExpansion.sval_of_secScal (hf α) (DegPre.trF Q (FractionRing R) mu).left z hJ
  have c1 : gs (DegPre.trF Q (FractionRing R) mu).left z ⊤ (scal (DegPre.BF Q (FractionRing R)).hom r₀) =
      gs (𝟙 _) z ⊤ (scal (DegPre.BF Q (FractionRing R)).hom r₀) := by
    rw [GlobalTheory.ExpInt.gs_scal, GlobalTheory.ExpInt.gs_scal, Over.w (DegPre.trF Q (FractionRing R) mu), Category.id_comp]
  have z0 : gs (𝟙 _) z ⊤ (scal (DegPre.BF Q (FractionRing R)).hom (0 : R)) = 0 := by
    rw [GlobalTheory.ExpInt.gs_scal]; exact (cstR _ z).map_zero
  simp only [Category.id_comp] at a1 fe
  rw [z0, zero_mul, add_zero, a1, fe, Over.comp_left, a2, c1]
  ring

theorem exists_fam {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) (k : ℕ) (f g : ∀ α, Q.SecB k α)
    (hf : ∀ mu α, ShiftEq Q k mu α (f α) (f (α + k • mu)) 0 (g (α + k • mu))) :
    ∃ F : Fam Q (FractionRing R) k, ∀ α, GeneratorPullback.SecScal Q.P.L (DegPre.famφ Q (FractionRing R) α) (DegPre.famε k)
      (F.s α) (Q.famφB α) (DegPre.famε k) (f α) (DegPre.prB Q (FractionRing R)).left 1 := by
  have hM := Q.P.isLB
  choose s hs using fun α => GlobalTheory.IndivisibleSection.exists_pull_val hM (f α) (DegPre.prB Q (FractionRing R)).left
    (φ' := DegPre.famφ Q (FractionRing R) α) (ε' := DegPre.famε k)
    (fun _ _ _ => Finset.prod_congr rfl fun i _ => by rw [DVR.GC.famφ_eq])
  refine ⟨⟨s, fun mu α u hu hc => (secRel_iff hM _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_⟩,
    fun α => DVR.SectionScalarValuation.secScal_of_sval hM fun y J hJ => (hs α _ (𝟙 _) y J hJ).symm⟩
  have e := hf mu α u hu hc y J hJ
  have z0 : gs (𝟙 _) y ⊤ (scal (DegPre.BF Q (FractionRing R)).hom (0 : R)) = 0 := by
    rw [GlobalTheory.ExpInt.gs_scal]; exact (cstR _ y).map_zero
  rw [hs _ _ (𝟙 _) y J hJ, hs _ _ _ y J hJ]
  simp only [Category.id_comp]
  rw [e, z0, zero_mul, add_zero, Over.comp_left]
  ring

end GlobalTheory.HeatValues

namespace GlobalTheory.HeatValues

theorem core {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (D : DegData R (maximalIdeal R))
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    (U : Unif (maximalIdeal R) D A G) (NL : LB G.left) (hN : U.LG.L = NL)
    (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] (oD : D.toPre.OAct O) (Y : Ray oD)
    (n : ℕ) (vH : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left)
    (hinv : ∀ a, IsInv Y.H (vH a) (dd a)) (Dr : Derivation ℤ R R)
    (h : Heat Y.H Y.q.left D.toPre.P.L dd ⇑Dr) (hbasic : IsBasic Y h) (hdef : HasDefect Y h (fun _ _ _ => 0))
    (i0 : h.J) (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω)
    (x : Sp Ω ⟶ Y.H.left) (x' : Sp Ω ⟶ G.left) (δ : Fin n → Derivation ℤ Ω Ω)
    (hcompl : IsAdicComplete ((maximalIdeal R).map φ) Ω) (hx : x ≫ Y.H.hom = spMap φ)
    (hx' : x' ≫ G.hom = spMap φ) (hδφ : ∀ a r, δ a (φ r) = 0)
    (hδ : ∀ a O f, ⊤ ≤ x ⁻¹ᵁ O → valR x O (dd a O f) = δ a (valR x O f))
    (hpx : GlobalTheory.FormalPoint.IsPointOf U.toUnifPre (Y.Φ (Over.mk (spMap φ)) (Over.homMk x hx))
      (Over.homMk x' hx'))
    (dΩ : Derivation ℤ Ω Ω) (hW : ⊤ ≤ x ⁻¹ᵁ h.W i0)
    (hd : ∀ O f, O ≤ h.W i0 → ⊤ ≤ x ⁻¹ᵁ O → valR x O (h.d i0 O f) = dΩ (valR x O f))
    (g : GlobalTheory.RayEv.Transport.Frame NL (x' ≫ 𝟙 G.left)) (hg : g.IsGen) :
    ∃ (e : Ωˣ), ∀ (k : ℕ), 1 ≤ k → ∀ (σ : SecM (𝟙 G.left) NL k) (ω : Ω), IsValue (𝟙 _) NL x' g k σ ω →
      ∃ (r : R) (σ' : SecM (𝟙 G.left) NL k) (ω' : Ω), r ≠ 0 ∧ IsValue (𝟙 _) NL x' g k σ' ω' ∧
        ω' = φ r * ((e : Ω) ^ k * ringOp ⇑dΩ (fun a => ⇑(δ a)) (φ.mapMatrix h.Θ) (fun a => φ (h.u a))
          (valR x _ (h.p i0)) (valR x _ (h.p' i0)) k (((e⁻¹ : Ωˣ) : Ω) ^ k * ω)) := by
  subst hN
  haveI := hcompl
  have hL := U.LG.isLB
  have hM := D.toPre.P.isLB
  set ξ := Y.Φ (Over.mk (spMap φ)) (Over.homMk x hx) with hξ
  have hlies : GlobalTheory.RayEv.Transport.Lies U.toUnifPre x' ξ.b.left := fun e Z r y hy => (hpx e Z r y hy).1
  obtain ⟨g', gM, hg', hgM, hfr⟩ :=
    GlobalTheory.TransportLimit.exists_frRel R (maximalIdeal R) D A G U.toUnifPre Ω φ x' hx' ξ.b.left hlies
  obtain ⟨ρ, hρ⟩ := GlobalTheory.FormalPoint.exists_ratio hL (φ := fun _ : PUnit => x') (ε := fun _ => 1)
    (φ' := fun _ : PUnit => x' ≫ 𝟙 G.left) (ε' := fun _ => 1) (fun _ _ _ => by simp only [Category.comp_id])
    g' g hg' hg
  have hxW : x (cpt Ω) ∈ h.W i0 := (top_le_iff_cpt x _).1 hW
  obtain ⟨JM, hJM, hJM0⟩ := exists_good D.toPre.P.L hM (cpt Ω) (fun _ : PUnit => x ≫ Y.q.left)
    (fun _ => h.j i0) (fun _ _ _ => rfl) (fun _ => h.le i0 hxW)
  obtain ⟨JL, hJL⟩ : ∃ JL, Good U.LG.L (cpt Ω) JL := by
    choose C hC using fun ψ : Sp Ω ⟶ G.left => exists_chart hL (ψ (cpt Ω))
    exact ⟨C, hC⟩
  have hbm : ⊤ ≤ (𝟙 (Sp Ω)) ⁻¹ᵁ LB.wchart D.toPre.P.L (fun _ : PUnit => ξ.b.left)
      (fun _ => JM (𝟙 _ ≫ ξ.b.left)) :=
    (top_le_iff_cpt _ _).2 (hJM.mem (fun _ : PUnit => ξ.b.left) (𝟙 _))
  have hu := toStkA_valR (𝟙 (Sp Ω)) _ (cpt Ω) hbm (gM.s fun _ => JM (𝟙 _ ≫ ξ.b.left))
  obtain ⟨uU, huU⟩ := GlobalTheory.FormalValue.isUnit_valR _ _ hbm (gM.s fun _ => JM (𝟙 _ ≫ ξ.b.left))
  have hκu : toStkA (cpt Ω) (uU : Ω) = (val gM (𝟙 _) (cpt Ω) JM).val := by rw [huU]; exact hu
  let ρU : Ωˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom.toMonoidHom ρ
  have hρc : ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp Ω) (z : Z), (gm r z ⊤ ρ).val = cstR r z (ρU : Ω) := fun Z r z => by
    rw [← gs_unit r z ⊤ (show r z ∈ (⊤ : (Sp Ω).Opens) from trivial)]
    show _ = gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom
      ((Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom ρ.val))
    rw [Iso.hom_inv_id_apply]
  refine ⟨ρU * uU⁻¹, fun k hk σ ω hσ => ?_⟩
  obtain ⟨r₀, σ₀, f₀, F, hr₀, hσ₀, hE₀, hF₀⟩ := exists_integral U k hk σ
  have hsh₀ := shiftEq_of_fam D.toPre k F f₀ r₀ hF₀
  choose f₁ hf₁ using fun α => GlobalTheory.T.torusInvariant_heatOperator_acts_on_fourierTerms R D O oD Y n vH dd hinv Dr h hbasic k α (f₀ α)
  have hsh₁ : ∀ mu α, ShiftEq D.toPre k mu α (f₁ α) (f₁ (α + k • mu)) 0 (f₀ (α + k • mu)) :=
    fun mu α => hdef k mu α (f₀ α) (f₁ α) (f₀ (α + k • mu)) (f₁ (α + k • mu)) hk (hsh₀ mu α) (hf₁ α)
      (hf₁ (α + k • mu))
  obtain ⟨F₁, hF₁⟩ := exists_fam D.toPre k f₁ f₀ hsh₁
  obtain ⟨s₁, ⟨r₁, hr₁, σ₁, f₂, -, hf₂, hE₁⟩, -⟩ := (U.expand k hk).2 F₁
  have hf₂₁ : ∀ α, DVR.SecIsMul D.toPre.P.A.hom r₁ (f₂ α) (f₁ α) := fun α =>
    GlobalTheory.IntegralExpansion.secIsMul_of_secScal hM _ (GlobalTheory.IntegralExpansion.prB_app_injective D.toPre) (hF₁ α)
      (by rw [Over.w (DegPre.prB D.toPre (FractionRing R))]; exact hf₂ α)
  obtain ⟨hdφ, hact⟩ := GlobalTheory.T.heatOperator_value_at_point_eq_ringOperator R Y.H D.toPre.P.A.left Y.q.left D.toPre.P.L n dd ⇑Dr h i0 Ω φ x hx δ hδ dΩ
    hW hd
  obtain ⟨s₀, t₀, hs₀, ht₀, had₀⟩ := GlobalTheory.RayEv.Transport.exists_adic_expansion R (maximalIdeal R) D A G
    U.toUnifPre Ω φ ξ (Over.homMk x' hx') hpx ξ.b.left rfl g' gM hg' hgM hfr k σ₀ f₀ hE₀
  obtain ⟨s₂, t₂, hs₂, ht₂, had₂⟩ := GlobalTheory.RayEv.Transport.exists_adic_expansion R (maximalIdeal R) D A G
    U.toUnifPre Ω φ ξ (Over.homMk x' hx') hpx ξ.b.left rfl g' gM hg' hgM hfr k σ₁ f₂ hE₁
  have j0le : h.W i0 ≤ LB.wchart D.toPre.P.L (fun _ : Fin 1 => Y.q.left) (fun _ => h.j i0) :=
    fun y hy => Set.mem_iInter.2 fun _ => h.le i0 hy
  have termv : ∀ (α : D.toPre.X) (fα : D.toPre.SecB k α) (τ : SecM Y.q.left D.toPre.P.L k),
      IsTerm Y k α fα τ →
      toStkA (cpt Ω) (valR x (h.W i0) (rsT (τ.f fun _ => h.j i0) (h.W i0))) =
        sval fα (𝟙 (Sp Ω) ≫ ξ.b.left) (cpt Ω) JM * (val (ξ.s α) (𝟙 (Sp Ω)) (cpt Ω) JM).val := by
    intro α fα τ hτ
    have e1 := hτ (Over.mk (spMap φ)) (Over.homMk x hx) (cpt Ω) JM hJM
    have e2 : (Over.homMk x hx : Over.mk (spMap φ) ⟶ Y.H) ≫ Y.q = ξ.b := (Y.Φ_b _).symm
    rw [e2] at e1
    rw [← gs_id_eq, GlobalTheory.NormGen.gs_valR (𝟙 _) x _ hW, Category.id_comp]
    erw [GlobalTheory.KS.DlogPol.gs_rsT x (cpt Ω) j0le hxW]
    refine Eq.trans ?_ e1
    exact (sval_of τ x (cpt Ω) JM _ fun _ => hJM0 PUnit.unit).symm
  let RO : Ω → Ω := ringOp ⇑dΩ (fun a => ⇑(δ a)) (φ.mapMatrix h.Θ) (fun a => φ (h.u a))
    (valR x _ (h.p i0)) (valR x _ (h.p' i0)) k
  have huu : (uU : Ω) ^ k * ((uU⁻¹ : Ωˣ) : Ω) ^ k = 1 := by rw [← mul_pow, Units.mul_inv, one_pow]
  have hρρ : (ρU : Ω) ^ k * ((ρU⁻¹ : Ωˣ) : Ω) ^ k = 1 := by rw [← mul_pow, Units.mul_inv, one_pow]
  have key : ∀ α, t₂ α = (φ r₁ * ((uU⁻¹ : Ωˣ) : Ω) ^ k) * RO (t₀ α * (uU : Ω) ^ k) := by
    intro α
    obtain ⟨τ, τ', hτ, hτ', hact'⟩ := hf₁ α
    have a0 := termv α (f₀ α) τ hτ
    have a1 := termv α (f₁ α) τ' hτ'
    have b0 := ht₀ α _ (𝟙 (Sp Ω)) (cpt Ω) JM hJM
    have b2 := ht₂ α _ (𝟙 (Sp Ω)) (cpt Ω) JM hJM
    erw [gs_id_eq] at b0 b2
    have m2 := GlobalTheory.IndivisibleSection.sval_of_secIsMul (hf₂₁ α) (𝟙 (Sp Ω) ≫ ξ.b.left) (cpt Ω) hJM
    have cc : (𝟙 (Sp Ω) ≫ ξ.b.left) ≫ D.toPre.P.A.hom = 𝟙 (Sp Ω) ≫ spMap φ := by
      rw [Category.assoc, Over.w ξ.b]; rfl
    rw [cc, cst_comp, cst_id] at m2
    have v0 : valR x (h.W i0) (rsT (τ.f fun _ => h.j i0) (h.W i0)) = t₀ α * (uU : Ω) ^ k := by
      apply toStkA_injective
      rw [a0, b0, map_mul, map_pow, hκu, Units.val_pow_eq_pow_val]
    have v1 : φ r₁ * valR x (h.W i0) (rsT (τ'.f fun _ => h.j i0) (h.W i0)) = t₂ α * (uU : Ω) ^ k := by
      apply toStkA_injective
      rw [map_mul, a1, map_mul, map_pow, hκu, ← Units.val_pow_eq_pow_val, ← b2, m2, _root_.mul_assoc]
    rw [hact k τ τ' hact', v0] at v1
    linear_combination (-(((uU⁻¹ : Ωˣ) : Ω) ^ k)) * v1 - t₂ α * huu
  let T : Ω →+ Ω := AddMonoidHom.mk' (fun y => RO (y * (uU : Ω) ^ k)) (fun a b => by
    simp only [RO, add_mul]; exact ringOp_add _ _ _ _ _ _ _ _ _)
  have hT : ∀ N y, y ∈ ((maximalIdeal R).map φ) ^ (N + 2) → T y ∈ ((maximalIdeal R).map φ) ^ N :=
    fun N y hy => ringOp_mem _ dΩ δ _ _ _ _ k N _ (Ideal.mul_mem_right _ _ hy)
  have hs₂e : s₂ = (φ r₁ * ((uU⁻¹ : Ωˣ) : Ω) ^ k) * T s₀ :=
    eq_of_adic _ T hT _ s₀ s₂ t₀ t₂ key had₀ had₂
  have hTs : T s₀ = RO (s₀ * (uU : Ω) ^ k) := rfl
  have hs0rel : s₀ * (ρU : Ω) ^ k = φ r₀ * ω := by
    have a : sval σ₀ (𝟙 _ ≫ x') (cpt Ω) JL = _ := hs₀ _ (𝟙 _) (cpt Ω) JL hJL
    have b := GlobalTheory.IndivisibleSection.sval_of_secIsMul hσ₀ (𝟙 _ ≫ x') (cpt Ω) hJL
    have c := hσ _ (𝟙 _) (cpt Ω) JL hJL
    have d := hρ _ (𝟙 _) (cpt Ω) JL hJL
    have cc : (𝟙 (Sp Ω) ≫ x') ≫ G.hom = 𝟙 _ ≫ spMap φ := by rw [Category.assoc, hx']
    rw [cc, cst_comp, cst_id] at b
    erw [gs_id_eq] at a c
    have e := b.symm.trans a
    rw [c] at e
    erw [d] at e
    rw [mul_pow, Units.val_mul, Units.val_pow_eq_pow_val (gm _ _ _ ρ), hρc, cstR_id] at e
    apply toStkA_injective
    rw [map_mul, map_mul, map_pow]
    refine (Units.mul_left_inj (val g (𝟙 _) (cpt Ω) JL ^ k)).1 ?_
    linear_combination (-1 : (Sp Ω).presheaf.stalk (cpt Ω)) * e
  let c' : R := -(2 * (k : R) * r₁ * Dr r₀)
  refine ⟨r₁ * r₀, DVR.SecOps.secAdd σ₁ (DVR.SecOps.secScale (scal G.hom c') σ),
    s₂ * (ρU : Ω) ^ k + φ c' * ω, mul_ne_zero hr₁ hr₀, ?_, ?_⟩
  · intro Z r z J hJ
    have a : sval σ₁ (r ≫ x') z J = _ := hs₂ Z r z J hJ
    have c := hσ Z r z J hJ
    have d := hρ Z r z J hJ
    rw [sval_secAdd _ _ _ _ hJ, GlobalTheory.UU.ShiftExp.sval_secScale _ _ _ _ hJ, a, c]
    erw [d]
    rw [GlobalTheory.ExpInt.gs_scal,
      Category.assoc, hx', cst_comp, mul_pow, Units.val_mul, Units.val_pow_eq_pow_val (gm r z ⊤ ρ), hρc]
    change cstR r z s₂ * _ + cstR r z (φ c') * (cstR r z ω * _) = cstR r z _ * _
    rw [map_add, map_mul, map_mul, map_pow]
    ring
  · rw [hs₂e, hTs, show (ρU * uU⁻¹)⁻¹ = uU * ρU⁻¹ by rw [mul_inv_rev, inv_inv], Units.val_mul, Units.val_mul]
    have hX : s₀ * (uU : Ω) ^ k = φ r₀ * (((uU : Ω) * ((ρU⁻¹ : Ωˣ) : Ω)) ^ k * ω) := by
      linear_combination (((ρU⁻¹ : Ωˣ) : Ω) ^ k * (uU : Ω) ^ k) * hs0rel - s₀ * (uU : Ω) ^ k * hρρ
    rw [hX]
    simp only [RO]
    rw [ringOp_mul dΩ δ _ _ _ _ k (φ r₀) _ (fun a => hδφ a r₀), hdφ r₀]
    simp only [c', map_neg, map_mul, map_natCast, map_ofNat]
    linear_combination (2 * (k : Ω) * φ r₁ * φ (Dr r₀) * ω) *
      ((ρU : Ω) ^ k * ((ρU⁻¹ : Ωˣ) : Ω) ^ k * huu + hρρ)

end GlobalTheory.HeatValues

theorem GlobalTheory.HeatValues.heat_values_at_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n : ℕ) (vH : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) Y.H)) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (vH a) (dd a)) → ∀ (v' : Fin n → TanM (𝟙 (Sp R)) t.G), (∀ a, GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ _ (tv (vH a))) (tv (v' a))) → ∀ (D : Derivation ℤ R R) (h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D), IsBasic Y h → HasDefect Y h (fun _ _ _ => 0) → ∀ (i0 : h.J) (Ω : Type) [CommRing Ω] [IsDomain Ω] [IsLocalRing Ω] (φ : R →+* Ω) (x : Sp Ω ⟶ Y.H.left) (x' : Sp Ω ⟶ t.G.left) (δ : Fin n → Derivation ℤ Ω Ω), IsAdicComplete ((maximalIdeal R).map φ) Ω → ∀ (hx : x ≫ Y.H.hom = spMap φ) (hx' : x' ≫ t.G.hom = spMap φ), (∀ a r, δ a (φ r) = 0) → (∀ a O f, ⊤ ≤ x ⁻¹ᵁ O → valR x O (dd a O f) = δ a (valR x O f)) → GlobalTheory.FormalPoint.IsPointOf P.U.toUnifPre (Y.Φ (Over.mk (spMap φ)) (Over.homMk x hx)) (Over.homMk x' hx') → ∀ (dΩ : Derivation ℤ Ω Ω), ⊤ ≤ x ⁻¹ᵁ h.W i0 → (∀ O f, O ≤ h.W i0 → ⊤ ≤ x ⁻¹ᵁ O → valR x O (h.d i0 O f) = dΩ (valR x O f)) → ∀ (g : GlobalTheory.RayEv.Transport.Frame t.PP.L (x' ≫ 𝟙 t.G.left)), g.IsGen → ∃ (e : Ωˣ) (p0 p0' : Ω), ∀ (k : ℕ), 1 ≤ k → ∀ (σ : SecM (𝟙 t.G.left) t.PP.L k) (ω : Ω), IsValue (𝟙 _) t.PP.L x' g k σ ω → ∃ (r : R) (σ' : SecM (𝟙 t.G.left) t.PP.L k) (ω' : Ω), r ≠ 0 ∧ IsValue (𝟙 _) t.PP.L x' g k σ' ω' ∧ ω' = φ r * ((e : Ω) ^ k * ringOp ⇑dΩ (fun a => ⇑(δ a)) (φ.mapMatrix h.Θ) (fun a => φ (h.u a)) p0 p0' k (((e⁻¹ : Ωˣ) : Ω) ^ k * ω)) := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt gam _ _ _ Y n vH dd hinv v' _ D h hbasic hdef i0 Ω _ _ _ φ x x' δ hcompl
    hx hx' hδφ hδ hpx dΩ hW hd g hg
  letI := H.starRing
  obtain ⟨e, he⟩ := GlobalTheory.HeatValues.core P.D P.U t.PP.L (congrArg (fun q => q.L) P.bundle) (𝓞 E) P.oD Y n vH dd hinv
    D h hbasic hdef i0 Ω φ x x' δ hcompl hx hx' hδφ hδ hpx dΩ hW hd g hg
  exact ⟨e, _, _, he⟩
