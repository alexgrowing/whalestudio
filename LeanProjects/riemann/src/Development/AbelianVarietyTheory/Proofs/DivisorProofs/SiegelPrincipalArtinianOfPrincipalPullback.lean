import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalSiegelOfGenericPrincipalSpecialAmple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleOfClosedProper
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.CechPic GlobalTheory.PrincipalIntegral
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ArtinPrinc

theorem surj_of_isPullback {P R₁ R₂ R₀ : CommRingCat.{0}} {f₁ : P ⟶ R₁} {f₂ : P ⟶ R₂} {g₁ : R₁ ⟶ R₀} {g₂ : R₂ ⟶ R₀}
    (hP : IsPullback f₁ f₂ g₁ g₂) (hs : Function.Surjective g₂) : Function.Surjective f₁ := by
  have h := hP.map (forget CommRingCat)
  intro r
  obtain ⟨r₂, hr₂⟩ := hs (g₁ r)
  obtain ⟨x, hx, -⟩ := ((Types.isPullback_iff _ _ _ _).1 h).2.2 r r₂ hr₂.symm
  exact ⟨x, hx⟩

theorem principal_of_pull : ∀ (g n : ℕ), 3 ≤ n → Odd n → ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → Nontrivial R₁ → ∀ (β : CommRingCat.of (cycAway n) ⟶ P) (c : SiegPre g n (zetaAway n) (Spec.map β)) (c₁ : SiegPre g n (zetaAway n) (Spec.map f₁ ≫ Spec.map β)), SiegPB c₁ c (Spec.map f₁) → c₁.Principal → c.Principal := by
  intro g n _ _ P R₁ R₂ R₀ f₁ f₂ g₁ g₂ hP hloc hart _ hs₂ _ β c c₁ hpb hc₁
  obtain ⟨φ, φ₂, hφ, hsq, hw, -⟩ := hpb
  obtain ⟨hA₁, hK₁⟩ := hc₁
  have hl : Out.Laws := GlobalTheory.abelianSchemeLaws_all.1
  have hf₁ : Function.Surjective f₁.hom := surj_of_isPullback hP hs₂
  let f := Spec.map f₁
  have hPc : cls c₁.P c₁.isLB = pull φ₂ (cls c.P c.isLB) := (cls_eq_iff _ (pull_isLB c.isLB _)).2 hw
  have hpair : ∀ {T : Over (Spec P)} {T' : Over (Spec R₁)} (u : T'.left ⟶ T.left) (a b : T ⟶ c.A)
      (a' b' : T' ⟶ c₁.A), a'.left ≫ φ = u ≫ a.left → b'.left ≫ φ = u ≫ b.left →
      pair (cls c₁.P c₁.isLB) a' b' = pull u (pair (cls c.P c.isLB) a b) := fun u a b a' b' ha hb => by
    rw [GlobalTheory.PrincipalIntegral.pair, GlobalTheory.PrincipalIntegral.pair, hPc, ← pull_comp, ← pull_comp, SiegelDescent.lift_comp_square hsq u a b a' b' ha hb]
  have hD : c.diag.IsLB := pull_isLB c.isLB _
  have hD₁ : c₁.diag.IsLB := pull_isLB c₁.isLB _
  have hd : cls c₁.diag hD₁ = pull φ (cls c.diag hD) :=
    hpair φ (𝟙 c.A) (𝟙 c.A) (𝟙 c₁.A) (𝟙 c₁.A) (by simp) (by simp)
  have hdiso : LBIso c₁.diag (c.diag.pull φ) := by
    refine (cls_eq_iff hD₁ (pull_isLB hD _)).1 ?_
    rw [cls_pull hD, hd]
  haveI := c.ab.proper
  haveI := c.ab.smooth
  have hA : Out.RelAmple c.A c.diag :=
    GlobalTheory.SharpLift.relAmple_of_closed_proper P c.A c.diag hD R₁ f₁.hom hf₁ c₁.A φ hφ.1 c₁.diag hD₁ hdiso hA₁
  refine ⟨hA, fun T x hx => ?_⟩
  obtain ⟨hpos, hdet⟩ := isE8_W8
  let G := Out.powObj c.A 8
  let pr : Fin 8 → (G ⟶ c.A) := Out.powPr c.A
  have hmon : ∀ u, IsMonHom (pr u) := fun u => inferInstance
  have huniv : ∀ (T : Over (Spec P)) (y : Fin 8 → (T ⟶ c.A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u := fun T y =>
    ⟨(Out.powIsLimit c.A 8).lift (Fan.mk T y), fun u => (Out.powIsLimit c.A 8).fac (Fan.mk T y) ⟨u⟩,
      fun x hx => (Out.powIsLimit c.A 8).uniq (Fan.mk T y) x fun u => hx u.as⟩
  have hG : IsAbelianScheme G := AbelianSchemeGerms.isAbelianScheme_powObj c.A c.ab 7
  let G' := (Over.pullback f).obj G
  let ψ : G'.left ⟶ G.left := Pdiv.PullbackComparison.pφ f G
  have hψ : IsGrpPullback G' G f ψ := Pdiv.PullbackComparison.isGrpPullback f G
  choose pr' hpr using fun u => SharpPull.exists_lift hψ hφ (pr u)
  have hmon' : ∀ u, IsMonHom (pr' u) := fun u => SharpPull.isMonHom_lift hψ hφ (hpr u)
  have huniv' : ∀ (T : Over (Spec R₁)) (y : Fin 8 → (T ⟶ c₁.A)), ∃! x : T ⟶ G', ∀ u, x ≫ pr' u = y u :=
    fun T y => by
    obtain ⟨x₀, hx₀, hu⟩ := huniv (Over.mk (T.hom ≫ f)) (fun u => pushHom hφ T (y u))
    obtain ⟨x, rfl⟩ := SharpPull.push_surj hψ x₀
    refine ⟨x, fun u => SharpPull.push_inj hφ ?_, fun x' hx' => SharpPull.push_inj hψ (hu _ fun u => ?_)⟩
    · rw [SharpPull.push_comp hψ hφ (hpr u), hx₀ u]
    · rw [← SharpPull.push_comp hψ hφ (hpr u), hx' u]
  let L := LB.LinComb c.P (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) fun uv => W8 uv.1 uv.2
  let L' := LB.LinComb c₁.P (K := Fin 8 × Fin 8) (fun uv => (lift (pr' uv.1) (pr' uv.2)).left)
    fun uv => W8 uv.1 uv.2
  have hL : L.IsLB := LB.isLB_linComb c.isLB _ _
  have hL' : L'.IsLB := LB.isLB_linComb c₁.isLB _ _
  have hLW : cls L hL = quad (cls c.P c.isLB) W8 pr := cls_linComb c.isLB _ _ _
  have hLW' : cls L' hL' = quad (cls c₁.P c₁.isLB) W8 pr' := cls_linComb c₁.isLB _ _ _
  have hiso : LBIso L' (L.pull ψ) := by
    refine (cls_eq_iff hL' (pull_isLB hL _)).1 ?_
    rw [cls_pull hL, hLW, hLW', quad, quad, map_sum]
    exact Finset.sum_congr rfl fun uv _ => by rw [map_zsmul, hpair ψ _ _ _ _ (hpr uv.1) (hpr uv.2)]
  have hadd := pair_mul c hl.globalFns hA
  have hadd' := pair_mul c₁ hl.globalFns hA₁
  have hK' : Out.KTriv G' L' := kTriv_of_kernel hadd' (pair_comm c₁) hmon' huniv' hL' hLW' hdet fun T x hx =>
    hK₁ T x ((cls_eq_zero_iff (pull_isLB c₁.isLB _)).1 hx)
  have hAL : Out.RelAmple G L :=
    PosDefAmple.relAmple_linComb_of_posDef hl.globalFns g n 8 _ _ _ _ c G pr W8 hmon huniv hA hpos
  haveI : IsLocalRing R₁ := IsLocalRing.of_surjective' f₁.hom hf₁
  haveI : IsLocalHom f₁.hom := Function.Surjective.isLocalHom f₁.hom hf₁
  have hK : Out.KTriv G L := GlobalTheory.SharpLift.kTriv_of_localHom P R₁ f₁.hom G hG L hL hAL G' ψ hψ L' hL' hiso hK'
  have hx' : pair (cls c.P c.isLB) (snd c.A T ≫ x) (fst c.A T) = 0 := (cls_eq_zero_iff (pull_isLB c.isLB _)).2 hx
  exact kernel_of_kTriv (n := 8) (G := G) hadd (pair_comm c) hmon huniv hL hLW (0 : Fin 8) hK T x hx'

end GlobalTheory.ArtinPrinc
