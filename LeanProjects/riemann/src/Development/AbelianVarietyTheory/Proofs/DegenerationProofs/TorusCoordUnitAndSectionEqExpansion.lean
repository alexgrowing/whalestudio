import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsLevelPoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsToStkAUnit
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsGTransport
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.IntegralSum
open GlobalTheory.FormalValue Filter Topology ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω}
variable {ρ : S.Real} {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (u : ρ.UTest p y₀)

theorem gPt_cancel {ψ ψ' : Sp (OO p) ⟶ u.D.toPre.P.A.left} (h : gPt p ≫ ψ = gPt p ≫ ψ') : ψ = ψ' := by
  have : IsProper u.D.toPre.P.A.hom := u.D.toPre.P.isAb.proper
  have := GlobalTheory.ZJ.AddExt.isDominant_gPt p
  exact ext_of_isDominant_of_isSeparated u.D.toPre.P.A.hom
    (ext_of_isDominant (gPt p) (by rw [← Category.assoc, h, Category.assoc])) (gPt p) h

theorem gtN_zero (c : Sp (OO p) ⟶ u.G.left) (g : GtPtF u.D.toPre (PadicAlgCl p)) (hc : c ≫ u.G.hom = spMap u.j)
    (h : u.Lev c g) : u.GtN g 0 := by
  obtain ⟨b₀, hb, H⟩ := h
  intro J hJ χ
  obtain ⟨ce, hce⟩ := exists_level_point u c hc 0
  obtain ⟨hbe, H⟩ := H 0 ce hce
  have := GlobalTheory.ZJ.AddExt.isDominant_gPt p
  have hb₀ : b₀ ≫ u.D.toPre.P.A.hom = spMap u.j := by
    refine ext_of_isDominant (gPt p) ?_
    rw [← Category.assoc, hb]
    refine (Over.w g.b).trans ?_
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl
  have ht : ⊤ ≤ ce ⁻¹ᵁ LB.wchart u.D.toPre.P.L (u.D.toPre.Oφ (u.U.gt 0).pG χ)
      (fun k => J (DegPre.gtφ u.D.toPre (PadicAlgCl p) g.b χ k)) := fun y _ => Set.mem_iInter.2 fun i => by
    have h1 := hJ (b₀ ≫ u.D.toPre.Oφ (𝟙 _) χ i) (by rw [Category.assoc, Oφ_over, hb₀])
    rw [← Category.assoc, hb, ← gtφ_eq] at h1
    exact (congrArg (fun q => q y ∈ u.D.toPre.P.L.U _) (level_Oφ u b₀ ce hbe χ i)).mpr (top_le_comp h1 _ trivial)
  obtain ⟨x, hx, hx'⟩ := H χ _ ht
  rw [← hx, norm_eq_one_of_isUnit u (e := 0) (by rw [hx']; exact isUnit_valR _ _ ht _)]
  simp

theorem parAt [ArithBase o Ω] (c : Sp (OO p) ⟶ u.G.left) (g : GtPtF u.D.toPre (PadicAlgCl p)) (a : u.PtC)
    (hc : c ≫ u.G.hom = spMap u.j) (ha : gPt p ≫ c = u.toG a) (h : u.Lev c g) (k : ℕ) : u.ParAt k a g := by
  obtain ⟨b₀, hb, H⟩ := h
  intro w hw l hl
  choose ce hce using exists_level_point u c hc
  have hbe := fun e => (H e (ce e) (hce e)).1
  choose d hd using fun y => exists_chart u.D.toPre.P.isLB y
  obtain ⟨jL, hjL⟩ := exists_chart u.U.LG.isLB (c (cpt _))
  have hL : ⊤ ≤ c ⁻¹ᵁ u.U.LG.L.U jL := (top_le_iff_cpt _ _).2 hjL
  have hM : ⊤ ≤ b₀ ⁻¹ᵁ u.D.toPre.P.L.U (d (b₀ (cpt _))) := (top_le_iff_cpt _ _).2 (hd _)
  obtain ⟨ω, ωe, hω0, hω, hωe⟩ := exists_omega u c b₀ ce hce hbe hL hM hc
  have hθ : ∀ θ : u.D.toPre.P.A.left ⟶ u.D.toPre.P.A.left,
      ⊤ ≤ (b₀ ≫ θ) ⁻¹ᵁ u.D.toPre.P.L.U (d ((b₀ ≫ θ) (cpt _))) := fun θ => (top_le_iff_cpt _ _).2 (hd _)
  choose x hx hx' using fun e χ => (H e (ce e) (hce e)).2 χ (fun i => d ((b₀ ≫ u.D.toPre.Oφ (𝟙 _) χ i) (cpt _)))
    (fun y _ => Set.mem_iInter.2 fun i => (congrArg (fun q => q y ∈ u.D.toPre.P.L.U _)
      (level_Oφ u b₀ (ce e) (hbe e) χ i)).mpr (top_le_comp (hθ _) _ trivial))
  have hx0 : ∀ e χ, x 0 χ = x e χ := fun e χ => Subtype.ext ((hx 0 χ).trans (hx e χ).symm)
  have HS := fun σ f hE => hasSum_integral u c b₀ ce hce hbe hL d hd (x 0) (fun e χ => by rw [hx0 e, hx']) ω ωe hω hωe
    (k := k) σ f hE
  let z : Sp (PadicAlgCl p) := cpt _
  obtain ⟨J, hJ, eJ⟩ := exists_good u.D.toPre.P.L u.D.toPre.P.isLB z
    (fun θ : u.D.toPre.P.A.left ⟶ u.D.toPre.P.A.left => gPt p ≫ b₀ ≫ θ) (fun θ => d ((b₀ ≫ θ) (cpt _)))
    (fun θ θ' e => by rw [gPt_cancel u e]) (fun θ => top_le_comp (hθ θ) _ trivial)
  let r : Sp (PadicAlgCl p) ⟶ (UnifPre.GF (G := u.G) (PadicAlgCl p)).left :=
    (lift (𝟙 (TFK (R := u.V) (PadicAlgCl p))) a).left
  have hr : r ≫ UnifPre.gFK (G := u.G) (PadicAlgCl p) = gPt p ≫ c := by
    rw [ha, ← Category.assoc]
    exact congrArg (fun t : u.PtC => t.left ≫ _) (lift_snd _ _)
  have hr' : r ≫ (fst (TFK (R := u.V) (PadicAlgCl p)) ((Over.pullback (jK u.V)).obj u.G)).left = 𝟙 _ :=
    congrArg (fun t => t.left) (lift_fst (𝟙 (TFK (R := u.V) (PadicAlgCl p))) a)
  obtain ⟨τ, τ0, hτ⟩ := exists_valF_secLin u.U.LG.isLB _ _ r hr' (gPt p ≫ c) hr k (l := l) (l' := jL)
    (by rw [ha]; exact hl) (top_le_comp hL _)
  obtain ⟨κ, κ0, hκ⟩ := exists_coef_secLin u.D.toPre (PadicAlgCl p) k g w hw z J hJ
  refine ⟨κ * ω ^ k * τ⁻¹, by simp [τ0, κ0, hω0], ?_⟩
  rintro σ' s ⟨n, cc, σ, f, hE, hσ, hs⟩
  have e₁ : valF r _ (σ'.f (fun _ => l)) =
      τ * ∑ i, cc i * ((secVal u.U.toUnifPre (σ i) c jL : OO p) : PadicAlgCl p) :=
    (hτ σ' n cc σ hσ).trans (congrArg (τ * ·) (Finset.sum_congr rfl fun i _ => congrArg (cc i * ·)
      (valR_spMap (OO p).subtype c _ (top_le_secChart hL) _)))
  have e₂ : ∀ χ, coef s g w χ = κ * ∑ i, cc i *
      ((valR b₀ _ ((f i χ).f (fun j => d ((b₀ ≫ u.D.toPre.famφB χ j) (cpt _)))) * x 0 χ : OO p) : PadicAlgCl p) := by
    intro χ
    refine (hκ s χ n cc (fun i => f i χ) (hs χ) (gPt p ≫ b₀) (fun j => d ((b₀ ≫ u.D.toPre.famφB χ j) (cpt _)))
      (fun i => d ((b₀ ≫ u.D.toPre.Oφ (𝟙 _) χ i) (cpt _))) hb (fun i => by rw [Category.assoc, eJ])
      (fun i => by rw [Category.assoc, eJ])).trans (congrArg (κ * ·) (Finset.sum_congr rfl fun i _ =>
        congrArg (cc i * ·) ?_))
    rw [MulMemClass.coe_mul]
    exact congrArg₂ (· * ·) (valR_spMap (OO p).subtype b₀ _
      ((top_le_iff_cpt _ _).2 (Set.mem_iInter.2 fun j => hd ((b₀ ≫ u.D.toPre.famφB χ j) (cpt _)))) _) (hx 0 χ).symm
  have hs' := (hasSum_sum (s := Finset.univ) fun i _ => (HS (σ i) (f i) (hE i)).mul_left (cc i)).mul_left κ
  show HasSum _ (_ * valF r _ (σ'.f (fun _ => l)))
  rw [e₁, funext e₂]
  refine (congrArg (HasSum _ ·) ?_).mp hs'
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp

theorem gtN_zero_and_parAt : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (c : Sp (OO p) ⟶ u.G.left) (g : GtPtF u.D.toPre (PadicAlgCl p)) (a : u.PtC), c ≫ u.G.hom = spMap u.j → gPt p ≫ c = u.toG a → u.Lev c g → u.GtN g 0 ∧ ∀ k, 1 ≤ k → u.ParAt k a g :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ u c g a hc ha h => ⟨gtN_zero u c g hc h, fun k _ => parAt u c g a hc ha h k⟩

end GlobalTheory.ZH.IntegralSum
end
