import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryExistsWithPrescribedPartsStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeRationalVectorsInAdelicTranslateStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompletedLatticeEqAdelicCompletionAndGram
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishingStatement
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
open NumberField MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.AllWt GlobalTheory.LevGeo
open scoped ENNReal
open IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MsRepsFwd

theorem latOf_congr (F E : Type) [Field F] [NumberField F] [Field E] [CharZero E] [Algebra F E]
    (n M : ℕ) (L : Set (Fin n → E)) (g κ : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA F E))
    (δ : Matrix (Fin n) (Fin n) E) (hinj : Function.Injective (inclR (F := F) (E := E) (Af F)))
    (hκ : ∀ z ∈ GlobalTheory.AdLat.hat F L, ∃ y ∈ GlobalTheory.AdLat.hat F L, κ *ᵥ z - z = M • y)
    (he : δ.map (inclR (F := F) (Af F)) * g = g * κ) :
    ∀ x ∈ GlobalTheory.AdLat.latOf F g L, ∃ y ∈ GlobalTheory.AdLat.latOf F g L, δ *ᵥ x - x = M • y := by
  intro x hx
  obtain ⟨z, hz, hzx⟩ := hx
  obtain ⟨y, hy, hzy⟩ := hκ z hz
  let i : E →+* GlobalTheory.AdLat.RA F E := inclR (F := F) (Af F)
  have hf : ∀ v : Fin n → E, GlobalTheory.AdLat.fv F v = i ∘ v := fun _ => rfl
  have e1 : i ∘ (δ *ᵥ x) = δ.map i *ᵥ (i ∘ x) := funext fun a => RingHom.map_mulVec i δ x a
  have e2 : i ∘ (δ *ᵥ x) - i ∘ x = M • (g *ᵥ y) := by
    rw [e1, ← hf x, ← hzx, Matrix.mulVec_mulVec, he, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_sub, hzy,
      Matrix.mulVec_smul]
  rcases Nat.eq_zero_or_pos M with hM | hM
  · subst hM
    have hx0 : δ *ᵥ x - x = 0 := by
      funext a
      apply hinj
      have e3 := congrFun e2 a
      simp only [Pi.sub_apply, Function.comp, zero_smul, Pi.zero_apply] at e3
      simp only [Pi.sub_apply, Pi.zero_apply, map_sub, map_zero]
      exact e3
    refine ⟨0, ⟨0, zero_mem _, ?_⟩, by rw [hx0, zero_smul]⟩
    rw [Matrix.mulVec_zero]
    funext a
    simp [GlobalTheory.AdLat.fv]
  · have hME : (M : E) ≠ 0 := by exact_mod_cast hM.ne'
    refine ⟨(M : E)⁻¹ • (δ *ᵥ x - x), ⟨y, hy, ?_⟩, by
      rw [← Nat.cast_smul_eq_nsmul E, smul_smul, mul_inv_cancel₀ hME, one_smul]⟩
    rw [hf]
    funext a
    have e3 := congrFun e2 a
    simp only [Pi.sub_apply, Function.comp, Pi.smul_apply, nsmul_eq_mul, smul_eq_mul, map_mul, map_sub] at e3 ⊢
    rw [e3, ← map_natCast i M, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hME, map_one, one_mul]

theorem herm_mulVec {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (G δ : Matrix (Fin r) (Fin r) E)
    (h : δᵀ * G * δ.map cc = G) (x y : Fin r → E) : herm G (δ *ᵥ x) (δ *ᵥ y) = herm G x y := by
  have hh : ∀ u v : Fin r → E, herm G u v = u ⬝ᵥ (G *ᵥ (fun b => cc (v b))) := by
    intro u v
    simp only [herm, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have hc : (fun b => cc ((δ *ᵥ y) b)) = δ.map cc *ᵥ (fun b => cc (y b)) := by
    funext b
    simp only [cc, Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
  rw [hh, hh, hc, dotProduct_comm (δ *ᵥ x), Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    dotProduct_comm _ x, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]

end GlobalTheory.MsRepsFwd

namespace GlobalTheory.MsRepsFwd

set_option maxHeartbeats 800000 in

theorem conj_rat_congr : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (Comp : Type) (X : Comp → Data D.host.E V.rank)
    (dict : GA D V → Σ k, Frame (X k).Ψ V.rank) (Kf : Subgroup (GA D V))
    (th : ∀ c, (X c).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (M : ℕ) (x0 : ∀ c, Frame (X c).Ψ V.rank),
    IsLevelK V M Kf → (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) → DictIsUnif V dict Kf th rfl →
    (∀ c, x0 c ∈ (X c).dom) →
    (∀ g, ∀ h ∈ GinfC V, ∃ γ' ∈ (X (dict g).1).Γ,
      dict (g * h) = ⟨(dict g).1, lact γ' (rmul (dict g).2 (archMat V th rfl x0 h (dict g).1))⟩) →
    (∀ c, (X c).Gm = -(V.gram)ᵀ) →
    ∀ (k : Comp) (g : GA D V), dict g = ⟨k, x0 k⟩ →
    ∀ Λk : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E),
      (Λk : Set (Fin V.rank → D.host.E)) = GlobalTheory.AdLat.latOf (maximalRealSubfield D.host.E) (finHom V g).1
        (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) →
    ∀ γ ∈ (X k).Γ, ∃ γ' : GL (Fin V.rank) D.host.E,
      (IsUStab (-(V.gram)ᵀ) Λk γ' ∧ ∀ x ∈ Λk, ∃ y ∈ Λk, (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E).mulVec x - x = M • y) ∧
      ∀ (τ : D.host.E →+* ℂ) (hτ : τ ∈ (X k).Ψ), archM V (th k ⟨τ, hτ⟩) g * (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ =
        (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map τ * archM V (th k ⟨τ, hτ⟩) g := by
  intro D V Comp X dict Kf th M x0 hK hth hD hdom hA hGm k g hg Λk hΛk γ hγ
  classical
  obtain ⟨-, -, -, -, -, hfib⟩ := hD
  obtain ⟨-, hrat, -, hsur⟩ := (GlobalTheory.T.adelicUnitary_exists_with_prescribed_parts D V).2 (X k).Ψ (th k) (X k).cmType (hth k)
  have hact : ∀ h, ∀ τ, mat (rmul (x0 k) (archMat V th rfl x0 h k)) τ = archM V (th k τ) h * mat (x0 k) τ := by
    intro h τ
    show mat (x0 k) τ * ((mat (x0 k) τ)⁻¹ * Matrix.reindex (finCongr rfl) (finCongr rfl) (archM V (th k τ) h) *
      mat (x0 k) τ) = _
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (hdom k τ).1),
      Matrix.one_mul]
    rfl
  have key : ∀ h ∈ GinfC V, ∃ γ'' ∈ (X k).Γ,
      dict (g * h) = ⟨k, lact γ'' (rmul (x0 k) (archMat V th rfl x0 h k))⟩ := by
    have := hA g
    rw [hg] at this
    exact this
  have h0 := ReciprocityTheory.ChartRestriction.G.AR.Up.PairUnfoldPf.gramE (X k) hγ
  rw [hGm k] at h0
  have h1 : ((γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map cc)ᵀ * V.gram * γ.1 = V.gram := by
    have := congrArg (fun A => -Aᵀ) h0
    simpa [Matrix.transpose_mul, Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg] using this
  have hun : ∀ τ : (X k).Ψ, ((γ.1.map τ.1).map (starRingEnd ℂ))ᵀ * V.gram.map τ.1 *
      γ.1.map τ.1 = V.gram.map τ.1 := by
    intro τ
    have hcc : (γ.1.map τ.1).map (starRingEnd ℂ) = (γ.1.map cc).map τ.1 := by
      ext a b
      exact (IsCMField.complexEmbedding_complexConj D.host.E τ.1 _).symm
    rw [hcc, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, h1]
  obtain ⟨h, hh, hw⟩ := hsur _ hun
  have hw' : ∀ τ : (X k).Ψ, archM V (th k τ) h = γ.1.map τ.1 := hw
  obtain ⟨γ'', h1', h2⟩ := key h hh
  obtain ⟨γ₀, hγ₀, κ, hκ, hdc⟩ := hfib g (g * h) (by
    rw [hg]
    refine ⟨γ'' * γ, mul_mem h1' hγ, ?_⟩
    rw [h2]
    congr 1
    funext τ
    show γ''.1.map τ.1 * mat (rmul (x0 k) (archMat V th rfl x0 h k)) τ =
      (γ'' * γ).1.map τ.1 * mat (x0 k) τ
    rw [hact, hw', Units.val_mul, Matrix.map_mul, Matrix.mul_assoc])
  obtain ⟨δ, hδ1, hδ2⟩ := hrat γ₀ hγ₀

  have hγ₀' := Subgroup.mem_subgroupOf.1 (show γ₀ ∈ HFinIn (AF D.host.F) _ (HSpace.gram V) from hγ₀)
  obtain ⟨δ', hδ', hδ'e⟩ := Subgroup.mem_map.1 hγ₀'
  haveI : Nontrivial (Af D.host.F) := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 D.host.F)
    exact (Formalism.UG.evalV D.host.F ⟨P, hP.isPrime,
      Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField D.host.F)⟩).toRingHom.domain_nontrivial
  haveI : Nontrivial (Af D.host.F ⊗[D.host.F] D.host.E) :=
    (Algebra.TensorProduct.includeLeft_injective (R := D.host.F) (S := D.host.F) (A := Af D.host.F) (B := D.host.E)
      (algebraMap D.host.F D.host.E).injective).nontrivial
  have hinj : Function.Injective (inclR (F := D.host.F) (E := D.host.E) (Af D.host.F)) :=
    (inclR (F := D.host.F) (E := D.host.E) (Af D.host.F)).injective
  have hfv : (finHom V γ₀).1 = γ₀.1.1.map
        (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)) := rfl
  have hδδ : δ = δ' := by
    apply Units.ext
    apply Matrix.map_injective hinj
    show δ.1.map (inclR (Af D.host.F)) = δ'.1.map (inclR (Af D.host.F))
    rw [← hδ2, hfv, ← hδ'e]
    ext a b
    show (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E))
      (inclR (AF D.host.F) (δ'.1 a b)) = inclR (Af D.host.F) (δ'.1 a b)
    simp [inclR]
  subst hδδ

  have hLg := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  have hU : (δ.1.map cc)ᵀ * V.gram * δ.1 = V.gram := by
    change Formalism.UG.cT _ δ.1 * V.gram * δ.1 = V.gram at hδ'
    convert hδ' using 3
    ext a b
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply]
    congr 1
  have hmat : δ.1ᵀ * -(V.gram)ᵀ * δ.1.map cc = -(V.gram)ᵀ := by
    have := congrArg (fun A => -Aᵀ) hU
    simpa [Matrix.transpose_mul, Matrix.mul_assoc, Matrix.neg_mul, Matrix.mul_neg] using this

  obtain ⟨-, hκ2⟩ := (hK κ⁻¹).1 (inv_mem hκ)
  obtain ⟨-, hκ3⟩ := (hK κ).1 hκ
  rw [hLg.1] at hκ2 hκ3
  have hh0 : finHom V h = 1 := hh
  have hfin : finHom V γ₀ * finHom V g = finHom V g * finHom V κ⁻¹ := by
    have : γ₀ * g = g * h * κ⁻¹ := by rw [hdc]; group
    rw [← map_mul, this, map_mul, map_mul, hh0, mul_one]
  have hfin' : finHom V γ₀⁻¹ * finHom V g = finHom V g * finHom V κ := by
    have : γ₀⁻¹ * g = g * κ * h⁻¹ := by
      calc γ₀⁻¹ * g = γ₀⁻¹ * (g * h) * h⁻¹ := by group
        _ = γ₀⁻¹ * (γ₀ * g * κ) * h⁻¹ := by rw [hdc]
        _ = g * κ * h⁻¹ := by group
    rw [← map_mul, this, map_mul, map_mul, map_inv, hh0, inv_one, mul_one]
  have hd : finHom V γ₀ = Formalism.UG.bc (inclR (F := D.host.F) (E := D.host.E) (Af D.host.F)) δ := Units.ext hδ2
  have he1 : δ.1.map (inclR (F := D.host.F) (Af D.host.F)) * (finHom V g).1 = (finHom V g).1 * (finHom V κ⁻¹).1 := by
    rw [← hδ2, ← Units.val_mul, hfin, Units.val_mul]
  have he2 : (δ⁻¹).1.map (inclR (F := D.host.F) (Af D.host.F)) * (finHom V g).1 = (finHom V g).1 * (finHom V κ).1 := by
    have e0 : finHom V γ₀⁻¹ = Formalism.UG.bc (inclR (F := D.host.F) (E := D.host.E) (Af D.host.F)) δ⁻¹ := by
      rw [map_inv, map_inv, hd]
    have e := congrArg Units.val hfin'
    rw [Units.val_mul, Units.val_mul, e0] at e
    exact e
  have C1 := latOf_congr D.host.F D.host.E V.rank M (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E))
    (finHom V g).1 (finHom V κ⁻¹).1 δ.1 hinj hκ2 he1
  have C2 := latOf_congr D.host.F D.host.E V.rank M (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E))
    (finHom V g).1 (finHom V κ).1 (δ⁻¹).1 hinj hκ3 he2
  have hmem : ∀ x, x ∈ Λk ↔ x ∈ GlobalTheory.AdLat.latOf D.host.F (finHom V g).1 (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) := by
    intro x
    rw [← SetLike.mem_coe, hΛk]
  have hcong : ∀ x ∈ Λk, ∃ y ∈ Λk, δ.1 *ᵥ x - x = M • y := by
    intro x hx
    obtain ⟨y, hy, e⟩ := C1 x ((hmem x).1 hx)
    exact ⟨y, (hmem y).2 hy, e⟩
  have hcong' : ∀ x ∈ Λk, ∃ y ∈ Λk, (δ⁻¹).1 *ᵥ x - x = M • y := by
    intro x hx
    obtain ⟨y, hy, e⟩ := C2 x ((hmem x).1 hx)
    exact ⟨y, (hmem y).2 hy, e⟩
  have hstab : ∀ x, x ∈ Λk ↔ δ.1 *ᵥ x ∈ Λk := by
    intro x
    constructor
    · intro hx
      obtain ⟨y, hy, e⟩ := hcong x hx
      rw [show δ.1 *ᵥ x = x + M • y by rw [← e]; abel]
      exact Λk.add_mem hx (nsmul_mem hy M)
    · intro hx
      obtain ⟨y, hy, e⟩ := hcong' _ hx
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at e
      rw [show x = δ.1 *ᵥ x + M • y by rw [← e]; abel]
      exact Λk.add_mem hx (nsmul_mem hy M)

  have hinf : infHom V γ₀ * infHom V g = infHom V g * infHom V h := by
    have h0 : infHom V κ⁻¹ = 1 := ((hK κ⁻¹).1 (inv_mem hκ)).1
    have : γ₀ * g = g * h * κ⁻¹ := by rw [hdc]; group
    rw [← map_mul, this, map_mul, map_mul, h0, mul_one]
  have hm : ∀ τ a b, archM V (th k τ) (a * b) = archM V (th k τ) a * archM V (th k τ) b := by
    intro τ a b
    unfold archM
    rw [map_mul, Units.val_mul, Matrix.map_mul]
  refine ⟨δ, ⟨⟨herm_mulVec _ _ hmat, hstab⟩, hcong⟩, fun τ hτ => ?_⟩
  rw [← hw' ⟨τ, hτ⟩, ← hδ1 ⟨τ, hτ⟩, ← hm, ← hm]
  have e : infHom V (g * h) = infHom V (γ₀ * g) := by rw [map_mul, map_mul, hinf]
  unfold archM
  rw [e]

end GlobalTheory.MsRepsFwd
