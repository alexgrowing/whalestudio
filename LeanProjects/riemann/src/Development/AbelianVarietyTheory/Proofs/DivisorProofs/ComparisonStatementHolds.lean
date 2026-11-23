import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SemiAbelianDvrExtensionsIsoCompatible
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericPointMemModuliOfMeetsAbelianLocus
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel

theorem cmpSt_holds : CmpSt := by
  intro E _ _ _ H Dw l l' Xo Xo' c c' W Y r ν hle _hov p _ _ T T' i iF hi io y₀ k y hy k' kO hkO hk' yT yyT hT hr
  letI := H.starRing
  letI := io.toAlgebra
  have hxeq := GlobalTheory.CompHt.IsHTFrame.x_eq hy
  obtain ⟨hTest, kO₀, P, ψ₀, z, hP, -, hch⟩ := hy
  obtain ⟨hkO₀, G, t', m₁, m₂, π₀, φ₀, hπ₀, hact₀, hφ₀, hgen₀, hψ₀, hL⟩ := hP
  have tr : ∀ {S S' : Scheme.{0}} {s : SAB H S} {s' : SAB H S'} {f g : S' ⟶ S}, f = g →
      ∀ m : SABMap s' s f, ∃ m' : SABMap s' s g, m'.φ = m.φ := by
    intro S S' s s' f g h m
    subst h
    exact ⟨m, rfl⟩

  have hkk : kO₀ = kO.comp i := RingHom.ext fun a => P.integers.hom_inj (by
    rw [hkO₀ a, RingHom.comp_apply, hkO (i a), hi, hk']; rfl)
  have hkk' : k'.comp iF = k.toRingHom := RingHom.ext fun a => hk' a
  have hii : (algebraMap T'.V T'.Fr).comp i = iF.comp (algebraMap T.V T.Fr) := RingHom.ext hi
  have hOO : (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp kO = k'.comp (algebraMap T'.V T'.Fr) := RingHom.ext hkO
  have hx' : yyT ≫ r ≫ pullback.fst _ _ = spMap iF ≫ y₀.1.x := by
    rw [← Category.assoc, hr, Category.assoc]
    congr 1
    exact pullback.lift_fst _ _ _

  obtain ⟨G', ⟨a⟩⟩ := exists_sab (spMap i) G
  obtain ⟨Yt', ⟨b⟩⟩ := exists_sab yT Y.t
  obtain ⟨t₂, ⟨q⟩⟩ := exists_sab yyT Y.oF.t
  obtain ⟨t₁, ⟨c₁⟩⟩ := exists_sab (spMap (algebraMap T'.V T'.Fr)) G'
  obtain ⟨n₁, hn₁⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ ν q
  obtain ⟨e₂, he₂⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ Y.m q
  obtain ⟨e₂', he₂'⟩ := tr (show yyT ≫ Y.jQ ≫ pullback.fst _ _ = spMap (algebraMap T'.V T'.Fr) ≫ yT from hT.symm) e₂
  obtain ⟨n₂, hn₂⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ b e₂'
  obtain ⟨e₁, he₁⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ a c₁
  obtain ⟨e₁', he₁'⟩ := tr (show spMap (algebraMap T'.V T'.Fr) ≫ spMap i = spMap iF ≫ spMap (algebraMap T.V T.Fr) by
    rw [spMap_spMap, spMap_spMap, hii]) e₁
  obtain ⟨d, hd⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m₂ e₁'
  obtain ⟨m₁', hm₁'⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m₁ d
  obtain ⟨m₁'', hm₁''⟩ := tr hx'.symm m₁'
  obtain ⟨κ, nn, hκ, hnn⟩ := GlobalTheory.sab_extensions_iso E H Dw l Xo T'.V T'.Fr _ G' Yt' t₁ t₂ m₁'' c₁ n₁ n₂

  have w₁ : π₀ ≫ G.G.hom = (P.G.hom ≫ spMap kO) ≫ spMap i := by
    rw [hπ₀.1.w, Category.assoc, spMap_spMap, hkk]
  let π₁ : P.G.left ⟶ G'.G.left := a.cart.1.lift π₀ (P.G.hom ≫ spMap kO) w₁
  have hπ₁a : π₁ ≫ a.φ = π₀ := a.cart.1.lift_fst _ _ _
  have hπ₁s : π₁ ≫ G'.G.hom = P.G.hom ≫ spMap kO := a.cart.1.lift_snd _ _ _
  have hπ₁ : IsGrpPullback P.G G'.G (spMap kO) π₁ :=
    a.cart.cancel (hπ₀.congr (by rw [spMap_spMap, hkk]) hπ₁a.symm) hπ₁s

  have w₂ : φ₀ ≫ t'.G.hom = (P.A.A.hom ≫ spMap k') ≫ spMap iF := by
    rw [hφ₀.1.w, Category.assoc, spMap_spMap, hkk']
  let ψ₁ : P.A.A.left ⟶ t₁.G.left := d.cart.1.lift φ₀ (P.A.A.hom ≫ spMap k') w₂
  have hψ₁d : ψ₁ ≫ d.φ = φ₀ := d.cart.1.lift_fst _ _ _
  have hψ₁s : ψ₁ ≫ t₁.G.hom = P.A.A.hom ≫ spMap k' := d.cart.1.lift_snd _ _ _
  have hψ₁ : IsGrpPullback P.A.A t₁.G (spMap k') ψ₁ :=
    d.cart.cancel (hφ₀.congr (by rw [spMap_spMap, hkk']) hψ₁d.symm) hψ₁s
  have key : ψ₁ ≫ c₁.φ = P.gen ≫ π₁ := by
    apply a.cart.1.hom_ext
    · rw [Category.assoc, Category.assoc, hπ₁a, ← he₁, ← he₁', hd, ← Category.assoc, hψ₁d, hgen₀]
    · rw [Category.assoc, Category.assoc, hπ₁s, c₁.cart.1.w, ← Category.assoc, hψ₁s, ← Category.assoc,
        P.gen_pull.1.w, Category.assoc, Category.assoc, spMap_spMap, spMap_spMap, hOO]
  refine ⟨P, π₁ ≫ nn.φ ≫ b.φ, ψ₁ ≫ κ.φ ≫ q.φ, ?_⟩
  have hψν : (ψ₁ ≫ κ.φ ≫ q.φ) ≫ ν.φ = ψ₀ := by
    rw [Category.assoc, Category.assoc, ← hn₁, hκ, hm₁'', hm₁', ← Category.assoc, hψ₁d, hψ₀]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, hTest, ?_, z, by rw [hψν]; exact hch⟩
  · rw [← Category.assoc, spMap_spMap, hOO, ← spMap_spMap, Category.assoc, hT, Category.assoc]
  · exact ((hπ₁.comp nn.cart).comp b.cart).congr (by rw [Category.comp_id]) (by rw [Category.assoc])
  · intro a₀
    have h1 : (P.oG.act a₀).left ≫ π₁ = π₁ ≫ (G'.act.act a₀).left := by
      apply a.cart.1.hom_ext
      · rw [Category.assoc, Category.assoc, hπ₁a, hact₀, a.act, ← Category.assoc, hπ₁a]
      · rw [Category.assoc, Category.assoc, hπ₁s, Over.w, hπ₁s, ← Category.assoc, Over.w]
    simp only [Category.assoc, reassoc_of% h1, reassoc_of% (nn.act a₀), b.act a₀]
  · exact ((hψ₁.comp κ.cart).comp q.cart).congr (by rw [Category.comp_id]) (by rw [Category.assoc])
  · have h2 : q.φ ≫ Y.m.φ = n₂.φ ≫ b.φ := by rw [← he₂, ← he₂', hn₂]
    rw [Category.assoc, Category.assoc, h2, ← Category.assoc κ.φ, ← hnn]
    simp only [Category.assoc]
    rw [reassoc_of% key]
  · exact LBIso.trans P.A.isLB (pull_isLB Xo.univ.t.PP.isLB _) (pull_isLB Y.oF.t.PP.isLB _) hL
      (GlobalTheory.LN.GenericPoint.lbIso_pull (GlobalTheory.LN.GenericPoint.lbIso_of_sabMap ν) _ hψν.symm).symm
  · apply pullback.hom_ext
    · rw [ptF, pullback.lift_fst, hxeq, Category.assoc, Category.assoc, hx', ← Category.assoc, spMap_spMap, hkk']
    · rw [ptF, pullback.lift_snd]
      simp only [Category.assoc]
      rw [reassoc_of% hr, ← Category.assoc, spMap_spMap, hkk', ptF, pullback.lift_snd, spMap_spMap]
      congr 1
      exact (RingHom.ext fun x => k.commutes x).symm

end GlobalTheory.FlatModel
