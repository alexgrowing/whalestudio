import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHalfIdem
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RationalPointsFinitePartSelfDualLatticeIff
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ScaledFiniteMatrixMemLattice
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteRationalPointsCompletedLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHomLatticeFinitelyGenerated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletedHomLatticeMultipleMemOpenLevel

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts GlobalTheory.FinWeil GlobalTheory.FinWeilO GlobalTheory.FockCompare GlobalTheory.VacUnique GlobalTheory.RatAut
open scoped TensorProduct Kronecker ComplexOrder nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RatLattice

open GlobalTheory.SplitScalar GlobalTheory.CompletedLatticeFinite

theorem relIndex_comap_comap {G H : Type} [AddCommGroup G] [AddCommGroup H] (f : G →+ H) (A B : AddSubgroup H)
    (h : ∀ b ∈ B, ∃ x, f x ∈ B ∧ b - f x ∈ A) : (A.comap f).relIndex (B.comap f) = A.relIndex B := by
  rw [AddSubgroup.relIndex_comap, ← AddSubgroup.relIndex_sup_right B A,
    ← AddSubgroup.relIndex_sup_right ((B.comap f).map f) A]
  congr 1
  refine le_antisymm (sup_le_sup_right (AddSubgroup.map_comap_le _ _) _) (sup_le (fun b hb => ?_) le_sup_right)
  obtain ⟨x, hx, hb⟩ := h b hb
  rw [← add_sub_cancel (f x) b]
  exact AddSubgroup.add_mem_sup ⟨x, hx, rfl⟩ hb

theorem fg_of_denom {E : Type} [Field E] [NumberField E] {m n : ℕ} (L : AddSubgroup (Matrix (Fin m) (Fin n) E))
    (d : E) (hd : d ≠ 0) (h : ∀ x ∈ L, ∀ i j, IsIntegral ℤ (d * x i j)) : L.FG := by
  let f : Matrix (Fin m) (Fin n) (𝓞 E) →+ Matrix (Fin m) (Fin n) E :=
    AddMonoidHom.mk' (fun x => Matrix.of fun i j => d⁻¹ * (x i j : E)) fun x y => by
      ext i j
      simp [mul_add]
  have e : L = (L.comap f).map f := by
    refine (AddSubgroup.map_comap_eq_self fun x hx => ⟨Matrix.of fun i j => ⟨d * x i j, h x hx i j⟩, ?_⟩).symm
    ext i j
    show d⁻¹ * (d * x i j) = x i j
    rw [inv_mul_cancel_left₀ hd]
  have h1 : (AddSubgroup.toIntSubmodule (L.comap f)).FG := IsNoetherian.noetherian _
  have h2 := h1.map f.toIntLinearMap
  rw [e]
  exact (Submodule.fg_iff_addSubgroup_fg _).1 h2

variable {D : D7} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
  {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem exists_denom_latQ (hS : ΛS.FG) (hT : ΛT.FG) :
    ∃ d : D.host.E, d ≠ 0 ∧ ∀ x ∈ latQ S T ΛS ΛT, ∀ i j, IsIntegral ℤ (d * x i j) := by
  classical
  obtain ⟨dS, hdS, hS'⟩ := exists_denom ΛS hS
  obtain ⟨dT, hdT, hT'⟩ := exists_denom ΛT hT
  obtain ⟨dA, hdA, hA'⟩ := D.host.AA.2
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ
    ((Finset.univ : Finset (Fin S.rank × Fin S.rank)).image fun p => S.gram p.1 p.2)
  have hdA0 : (dA : D.host.E) ≠ 0 := by
    have := nonZeroDivisors.ne_zero hdA
    exact_mod_cast this
  have hd : (dA : D.host.E) * dT * (star dS * (y : D.host.E)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hdA0 hdT) (mul_ne_zero (star_ne_zero.2 hdS) (by exact_mod_cast hy0))
  set d : D.host.E := (dA : D.host.E) * dT * (star dS * (y : D.host.E)) with hdd
  have hgen : ∀ a ∈ D.host.AA, ∀ s ∈ ΛS, ∀ t ∈ ΛT, ∀ i j,
      IsIntegral ℤ (d * (a * t i * ∑ k, star (s k) * S.gram k j)) := by
    intro a ha s hs t ht i j
    have e : d * (a * t i * ∑ k, star (s k) * S.gram k j) =
        ((dA : D.host.E) * a) * (dT * t i) * ∑ k, star (dS * s k) * ((y : D.host.E) * S.gram k j) := by
      simp only [hdd, Finset.mul_sum, star_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e]
    refine IsIntegral.mul (IsIntegral.mul ?_ (hT' t ht i)) (IsIntegral.sum _ fun k _ =>
      (isIntegral_star D (hS' s hs k)).mul ?_)
    · obtain ⟨b, hb⟩ := hA' a ha
      have : (dA : D.host.E) * a = (b : D.host.E) := hb.symm
      rw [this]
      exact b.isIntegral_coe
    · have := hy (S.gram k j) (Finset.mem_image.2 ⟨(k, j), Finset.mem_univ _, rfl⟩)
      simpa [zsmul_eq_mul] using this
  have hlat : ∀ l ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True),
      ∀ i j, finPart D (l i j) ∈ GlobalTheory.AdLat.hat1 D.host.F
        ((FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ d⁻¹ : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Set D.host.E) := by
    intro l hl i j
    induction hl using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hw
      exact AddSubgroup.subset_closure ⟨α, hα, _, (mem_spanSingleton_inv d hd _).2 (hgen a ha s hs t ht i j), rfl⟩
    | zero => rw [Matrix.zero_apply, RingHom.map_zero]; exact zero_mem _
    | add x z _ _ hx hz => rw [Matrix.add_apply, RingHom.map_add]; exact add_mem hx hz
    | neg x _ hx => rw [Matrix.neg_apply, RingHom.map_neg]; exact neg_mem hx
  exact ⟨d, hd, fun x hx i j =>
    (mem_spanSingleton_inv d hd _).1 (((GlobalTheory.AdLat.adelicCompletion_fractionalIdeal_properties D.host.F D.host.E).2.1 _ (x i j)).1 (hlat _ hx i j))⟩

theorem exists_rat_add_nsmul (Λ : AddSubgroup (WO S T)) (hinf : ∀ u ∈ Λ, u.map (infPart D) = 0)
    (happ : ∀ γ : WO S T, γ.map (infPart D) = 0 → ∃ ρ ∈ ratL T S, ∃ u ∈ Λ, (γ - ρ - u).map (finPart D) = 0)
    {z : WO S T} (hz : z.map (infPart D) = 0) {N : ℕ} (hN : 0 < N) :
    ∃ y, ∃ u ∈ Λ, z = finRat S T y + N • u := by
  obtain ⟨γ, hγ, hNγ⟩ := GlobalTheory.RatSelfDual.exists_div hz hN
  obtain ⟨ρ, ⟨y₀, hy₀⟩, u, hu, hz⟩ := happ γ hγ
  have hγe : γ = finRat S T y₀ + u := by
    refine Matrix.ext fun i j => adele_ext ?_ ?_
    · have e0 : infPart D (γ i j) = 0 := congrFun (congrFun hγ i) j
      have e1 : infPart D (finRat S T y₀ i j) = 0 := congrFun (congrFun (finRat_inf S T y₀) i) j
      have e2 : infPart D (u i j) = 0 := congrFun (congrFun (hinf u hu) i) j
      rw [Matrix.add_apply, RingHom.map_add, e0, e1, e2, add_zero]
    · have e0 : finPart D (γ i j - ρ i j - u i j) = 0 := congrFun (congrFun hz i) j
      have e1 : finPart D (finRat S T y₀ i j) = finPart D (ρ i j) := by rw [← hy₀]; rfl
      rw [RingHom.map_sub, RingHom.map_sub, sub_sub, sub_eq_zero] at e0
      rw [Matrix.add_apply, RingHom.map_add, e1, e0]
  exact ⟨N • y₀, u, hu, by rw [← hNγ, hγe, nsmul_add, (finRat S T).map_nsmul]⟩

theorem actO_inv_actO (g : GA D S) (h : GA D T) (x : XF S T) :
    rhoF S T (g, h) (rhoF S T (g⁻¹, h⁻¹) x) = x ∧ rhoF S T (g⁻¹, h⁻¹) (rhoF S T (g, h) x) = x := by
  constructor
  · rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_inv_cancel, Prod.mk_one_one, map_one,
      Module.End.one_apply]
  · rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, Prod.mk_one_one, map_one,
      Module.End.one_apply]

theorem mem_map_rhoF (A : Submodule (𝓞 D.host.E) (XF S T)) (g : GA D S) (h : GA D T) (x : XF S T) :
    x ∈ A.map (rhoF S T (g, h)) ↔ rhoF S T (g⁻¹, h⁻¹) x ∈ A :=
  ⟨fun ⟨y, hy, e⟩ => by rwa [← e, (actO_inv_actO g h y).2], fun hx => ⟨_, hx, (actO_inv_actO g h x).1⟩⟩

def finX (S T : HSp D) : Matrix (Fin T.rank) (Fin S.rank) D.host.E →+ XF S T :=
  AddMonoidHom.mk' (fun x => XF.mk (finRat S T x) (finRat_inf S T x)) fun x y => XF.ext ((finRat S T).map_add x y)

theorem rhoF_finX {g : GA D S} {h : GA D T} {a : Matrix (Fin S.rank) (Fin S.rank) D.host.E}
    {b : Matrix (Fin T.rank) (Fin T.rank) D.host.E} (ha : Formalism.L2.Theta.mt S g = a.map (incA D))
    (hb : Formalism.L2.Theta.mt T h⁻¹ = b.map (incA D)) (x : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    rhoF S T (g⁻¹, h⁻¹) (finX S T x) = finX S T (b * x * a) := by
  apply XF.ext
  show actO S T g⁻¹ h⁻¹ (finRat S T x) = finRat S T (b * x * a)
  rw [finRat_eq, finRat_eq, actO_smul, actO, inv_inv, ha, hb]
  congr 1
  exact ((Matrix.map_mul (f := incA D)).trans (congrArg (· * a.map (incA D)) (Matrix.map_mul (f := incA D)))).symm

theorem latQ_selfDual_fg_full_index : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → SelfDual (gamQ ψ S T) (latQ S T ΛS ΛT) ∧ (latQ S T ΛS ΛT).toAddSubgroup.FG ∧ (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ N : ℕ, 0 < N ∧ N • x ∈ latQ S T ΛS ΛT) ∧ ∀ (g : GA D S) (h : GA D T) (a : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (b : Matrix (Fin T.rank) (Fin T.rank) D.host.E), Formalism.L2.Theta.mt S g = a.map (incA D) → Formalism.L2.Theta.mt T h⁻¹ = b.map (incA D) → idx (latF S T ΛS ΛT) ((latF S T ΛS ΛT).map (rhoF S T (g, h))) = (latQ S T ΛS ΛT).toAddSubgroup.relIndex ((latQ S T ΛS ΛT).toAddSubgroup.comap (sandw b a).toAddMonoidHom) := by
  intro D ψ hψ S T ΛS ΛT hS hT
  obtain ⟨hdual, happ, -⟩ := GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT
  have hden := GlobalTheory.VacUnique.Den.exists_nsmul_finRat_mem D S T ΛS ΛT hS.1 hT.1
  refine ⟨fun x => ?_, ?_, fun x => ?_, fun g h a b ha hb => ?_⟩
  · refine (GlobalTheory.RatSelfDual.finRat_mem_iff D S T ψ _ hψ (fun u hu => latO_fin hu) hdual happ hden x).trans ?_
    exact forall₂_congr fun y _ => (GlobalTheory.RatSelfDual.psi_fin_iff hψ S T x y).symm
  · obtain ⟨d, hd, h⟩ := exists_denom_latQ (S := S) (T := T) hS.1.fg hT.1.fg
    exact fg_of_denom _ d hd h
  · obtain ⟨N, hN, h⟩ := hden x
    exact ⟨N, hN, by rwa [mem_latQ, map_nsmul]⟩
  · obtain ⟨N, hN, hmov⟩ := (GlobalTheory.LatLevel.level_of_generators D S T ΛS ΛT hS hT
      (GlobalTheory.LatFinGen.latO_finitely_generated D S T ΛS ΛT hS hT)).2 g⁻¹ h⁻¹
    rw [GlobalTheory.FinWeil.idx, ← relIndex_comap_comap (finX S T)]
    · congr 1
      refine AddSubgroup.ext fun x => (mem_map_rhoF _ g h (finX S T x)).trans ?_
      rw [rhoF_finX ha hb]
      rfl
    · intro z hz
      obtain ⟨y, u, hu, e⟩ := exists_rat_add_nsmul _ (fun u hu => latO_fin hu) happ z.fin hN
      have e' : z = finX S T y + N • XF.mk u (latO_fin hu) := XF.ext e
      have h1 : N • XF.mk u (latO_fin hu) ∈ (latF S T ΛS ΛT).map (rhoF S T (g, h)) := by
        rw [mem_map_rhoF, map_nsmul]
        exact hmov u hu
      refine ⟨y, ?_, ?_⟩
      · rw [← sub_eq_iff_eq_add.2 e']
        exact sub_mem hz h1
      · rw [sub_eq_iff_eq_add'.2 e']
        exact nsmul_mem (show XF.mk u (latO_fin hu) ∈ latF S T ΛS ΛT from hu) N

end GlobalTheory.RatLattice

end
