import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.GenBCFrameR
import Formalism.LocalToGlobal.ProjectiveLattices.FrCovA

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LocM.FrameBC

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj GlobalTheory.LieMet
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {S T : Type} [CommRing S] [CommRing T] {x : Sp S ⟶ X}

theorem tv_sum' {κ : Type} (s : Finset κ) (f : κ → TanM x t.G) : tv (∑ i ∈ s, f i) = ∏ i ∈ s, tv (f i) := by
  simp only [tv, toMul_sum, Subgroup.val_finset_prod]

def Full {κ : Type} [Fintype κ] (v : κ → TanM x t.G) : Prop :=
  ∀ n : TanM x t.G, ∃! a : κ → S, n = ∑ k, a k • v k

theorem full_equiv {κ κ' : Type} [Fintype κ] [Fintype κ'] (e : κ' ≃ κ) {v : κ → TanM x t.G} (hv : Full v) :
    Full (fun i => v (e i)) := fun n => by
  obtain ⟨a, ha, hu⟩ := hv n
  refine ⟨fun i => a (e i), ha.trans (e.sum_comp (fun k => a k • v k)).symm, fun b hb => ?_⟩
  have := hu (fun k => b (e.symm k)) (hb.trans (by
    rw [← e.sum_comp]; simp only [Equiv.symm_apply_apply]))
  funext i; rw [← this]; simp

theorem full_iff {m : ℕ} {G' : Over (Sp S)} [GrpObj G'] [IsCommMonObj G'] {Φ : G'.left ⟶ t.G.left}
    (h : IsGrpPullback G' t.G x Φ) {u : Fin m → (epsR S ⟶ G')} {v : Fin m → TanM x t.G}
    (e : ∀ i, pushHom h (epsR S) (u i) = tv (v i)) : IsLieBasis u ↔ Full v := by
  have key : ∀ a p n, pushHom h (epsR S) p = tv n → (IsLieComb a u p ↔ n = ∑ k, a k • v k) := fun a p n hp => by
    rw [isLieComb_iff h, hp]
    simp only [e]
    exact ⟨fun q => tanM_ext (q.trans (by rw [tv_sum']; rfl)), fun q => (congrArg tv q).trans (by rw [tv_sum']; rfl)⟩
  refine ⟨fun hu n => ?_, fun hv => ⟨fun i => (isTangent_iff h _).2 (by rw [e]; exact tv_mem _), fun p hp => ?_⟩⟩
  · obtain ⟨p, hp⟩ := push_surj h (tv n)
    simpa only [key _ p n hp] using hu.2 p ((isTangent_iff h p).2 (by rw [hp]; exact tv_mem n))
  · simpa only [key _ p (mkT _ ((isTangent_iff h p).1 hp)) rfl] using hv (mkT _ ((isTangent_iff h p).1 hp))

def resM (ψ : S →+* T) (n : TanM x t.G) : TanM (spMap ψ ≫ x) t.G := tanOf (isTan_map ψ rfl (isTan_tv n))

theorem full_bc {m : ℕ} (ψ : S →+* T) {v : Fin m → TanM x t.G} (hv : Full v) : Full fun i => resM ψ (v i) := by
  have h₀ := isGrpPullback_pullback t.G x
  have h := isGrpPullback_pullback t.G (spMap ψ ≫ x)
  choose u hu using fun i => push_surj h₀ (tv (v i))
  choose u' hu' using fun i => push_surj h (tv (resM ψ (v i)))
  have := t.semi.smooth
  have : Smooth ((Over.pullback x).obj t.G).hom := show Smooth (pullback.snd _ _) from inferInstance
  refine (full_iff h hu').1 (Chart.frameLieBCR _ ((full_iff h₀ hu).2 hv) ψ (Chart.isGrpPullback_factor x (spMap ψ) h)
    (fun a b v hv => push_inj h (by
      have := smT_add _ _ ((isTangent_iff h v).1 ((Chart.isTan_iff _).1 hv)) a b
      rw [← push_scK h, ← push_scK h, ← push_scK h, ← map_mul] at this
      exact this)) (fun i => (isTangent_iff h _).2 (by rw [hu']; exact tv_mem _)) fun i => ?_)
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, Category.assoc]
    exact (congrArg (fun q => q.left) (hu' i)).trans (congrArg (_ ≫ ·) (congrArg (fun q => q.left) (hu i)).symm)
  · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, Over.w (u' i), Category.assoc]
    refine Eq.trans ?_ (congrArg (_ ≫ ·) (Over.w (u i)).symm)
    exact (spMap_comp_spMap _ _).trans ((congrArg spMap (PullbackSections.dualMap_comp_alg _).symm).trans (spMap_comp_spMap _ _).symm)

variable {l : Level H} (c : Coeff l) [Algebra c.F S]

theorem eig_iff (τ : E →+* ℂ) (n : TanM x t.G) :
    (∀ a : 𝓞 E, (tv n).left ≫ (t.act.act a).left = spMap (epsMul (algebraMap c.F S (embK c τ a))) ≫ (tv n).left) ↔
      IsEigV (actR (x0 := x) (S := S) t.act) (embK c τ) n :=
  forall_congr' fun _ => ⟨fun h => tan_ext h, fun h => congrArg (fun V => (tv V).left) h⟩

theorem eig_comb' (τ : E →+* ℂ) {m : ℕ} (v : Fin m → TanM x t.G)
    (hv : ∀ i, IsEigV (actR (x0 := x) (S := S) t.act) (embK c τ) (v i)) (a : Fin m → S) :
    IsEigV (actR (x0 := x) (S := S) t.act) (embK c τ) (∑ i, a i • v i) := by
  intro b
  rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, hv i b, smul_comm]

theorem full_of_eig {d : (E →+* ℂ) → ℕ} (v : ∀ τ, Fin (d τ) → TanM x t.G)
    (hv : ∀ τ i, IsEigV (actR (x0 := x) (S := S) t.act) (embK c τ) (v τ i))
    (hb : ∀ τ n, IsEigV (actR (x0 := x) (S := S) t.act) (embK c τ) n → ∃! a : Fin (d τ) → S, n = ∑ i, a i • v τ i) :
    Full (fun k : (Σ τ : E →+* ℂ, Fin (d τ)) => v k.1 k.2) := by
  classical
  intro m
  have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
  obtain ⟨α, hinj, ⟨f, hf, hfs⟩, hN⟩ :=
    exists_sepElt (E := E) (F := c.F) c.F.val.toRingHom (embK c) (fun τ a => embK_coe c τ a)
  let ρ := actR (x0 := x) (S := S) t.act
  have hsum : ∑ τ, proj ρ (embK c) α τ m = m := by
    have := congrArg (fun e : Module.End S (TanM x t.G) => e m) (sum_proj ρ (embK c) α hinj)
    simpa [LinearMap.sum_apply] using this
  have hE : ∀ τ, IsEigV ρ (embK c τ) (proj ρ (embK c) α τ m) := fun τ =>
    eig_of_alpha ρ (embK c) α hN τ (proj_eig_alpha ρ (embK c) α hinj f hf hfs τ m)
  choose a ha hu using fun τ => hb τ (proj ρ (embK c) α τ m) (hE τ)
  refine ⟨fun k => a k.1 k.2, ?_, fun b hb => ?_⟩
  · show m = ∑ k : (Σ τ : E →+* ℂ, Fin (d τ)), a k.1 k.2 • v k.1 k.2
    rw [Fintype.sum_sigma]
    conv_lhs => rw [← hsum]
    exact Finset.sum_congr rfl fun τ _ => ha τ
  · have hb' : m = ∑ k : (Σ τ : E →+* ℂ, Fin (d τ)), b k • v k.1 k.2 := hb
    rw [Fintype.sum_sigma] at hb'
    funext k
    obtain ⟨τ, i⟩ := k
    have hn := proj_sum_eig ρ (embK c) α hinj (fun τ => ∑ i, b ⟨τ, i⟩ • v τ i)
      (fun τ => eig_comb' c τ _ (fun i => hv τ i) _) τ
    rw [← hb'] at hn
    have := hu τ (fun i => b ⟨τ, i⟩) hn
    exact congrFun this i

theorem eig_of_full {d : (E →+* ℂ) → ℕ} (v : ∀ τ, Fin (d τ) → TanM x t.G)
    (hE : ∀ τ i, IsEigV (actR (x0 := x) (S := S) t.act) (embK c τ) (v τ i))
    (hfull : Full (fun k : (Σ τ : E →+* ℂ, Fin (d τ)) => v k.1 k.2)) (τ : E →+* ℂ) (w : TanM x t.G)
    (hm : IsEigV (actR (x0 := x) (S := S) t.act) (embK c τ) w) : ∃! a : Fin (d τ) → S, w = ∑ i, a i • v τ i := by
  classical
  have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
  obtain ⟨α, hinj, -, -⟩ :=
    exists_sepElt (E := E) (F := c.F) c.F.val.toRingHom (embK c) (fun τ a => embK_coe c τ a)
  let ρ := actR (x0 := x) (S := S) t.act
  have hproj : proj ρ (embK c) α τ w = w := by
    have := proj_sum_eig ρ (embK c) α hinj (fun σ' => if σ' = τ then w else 0)
      (fun σ' => by
        split_ifs with h
        · subst h; exact hm
        · exact fun a => by simp) τ
    simpa [Finset.sum_ite_eq'] using this
  obtain ⟨A, hA, hAu⟩ := hfull w
  have hcomp : proj ρ (embK c) α τ w = ∑ i, A ⟨τ, i⟩ • v τ i := by
    have h1 := proj_sum_eig ρ (embK c) α hinj (fun σ' => ∑ i, A ⟨σ', i⟩ • v σ' i)
      (fun σ' => eig_comb' c σ' _ (fun i => hE σ' i) _) τ
    rw [← Fintype.sum_sigma (fun k : (Σ σ : E →+* ℂ, Fin (d σ)) => A k • v k.1 k.2), ← hA] at h1
    exact h1
  refine ⟨fun i => A ⟨τ, i⟩, hproj.symm.trans hcomp, fun b hb => ?_⟩
  have hb : w = ∑ i, b i • v τ i := hb
  let B : (Σ σ : E →+* ℂ, Fin (d σ)) → S := fun k => if h : k.1 = τ then b (h ▸ k.2) else 0
  have hB : w = ∑ k, B k • v k.1 k.2 := by
    rw [Fintype.sum_sigma, hb, Finset.sum_eq_single τ]
    · exact Finset.sum_congr rfl fun i _ => by simp [B]
    · intro σ _ hσ
      exact Finset.sum_eq_zero fun i _ => by simp [B, hσ]
    · intro h; exact absurd (Finset.mem_univ τ) h
  have := hAu B hB
  funext i
  have := congrFun this ⟨τ, i⟩
  simpa [B] using this

end GlobalTheory.LocM.FrameBC

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM
  ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.LieMet GlobalTheory.LocM.FrameBC in

theorem GlobalTheory.LocM.isFrame_bc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (X : Scheme.{0}) (t : SAB H X) (R S : Type) [CommRing R] [CommRing S] (f : c.F →+* R) (φ : R →+* S) (x : Sp R ⟶ X) (u : Vecs Dw t R), GlobalTheory.LocM.IsFrame t f x u → GlobalTheory.LocM.IsFrame t (φ.comp f) (spMap φ ≫ x) (u.bc φ) := by
  intro E _ _ _ H Dw l c X t R S _ _ f φ x u hu
  letI : Algebra c.F R := f.toAlgebra
  letI : Algebra c.F S := (φ.comp f).toAlgebra
  let v : ∀ τ, Fin (Dw.mult τ) → TanM x t.G := fun τ i => tanOf (hu.1 τ i).1
  have he : ∀ τ i (a : 𝓞 E), u.bc φ τ i ≫ (t.act.act a).left =
      spMap (epsMul ((φ.comp f) (embK c τ a))) ≫ u.bc φ τ i := fun τ i a => by
    show (spMap (dualMap φ) ≫ u τ i) ≫ _ = _ ≫ spMap (dualMap φ) ≫ u τ i
    rw [Category.assoc, (hu.1 τ i).2 a, ← Category.assoc, Formalism.L2.Pj.FrCov.eps_dual, Category.assoc, RingHom.comp_apply]
  have h1 := full_of_eig c v (fun τ i => (eig_iff c τ (v τ i)).1 (hu.1 τ i).2) fun τ n hn => by
    exact (existsUnique_congr fun a => LieMet.isComb_iff (v τ) a n).1 (hu.2 τ _ (isTan_tv n) ((eig_iff c τ n).2 hn))
  have h2 : Full fun k : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) => resM φ (v k.1 k.2) := by
    have h := full_equiv (eB Dw).symm (full_bc φ (full_equiv (eB Dw) h1))
    exact (funext fun k => congrArg (fun j : IxB Dw => resM φ (v j.1 j.2)) ((eB Dw).apply_symm_apply k)) ▸ h
  refine ⟨fun τ i => ⟨isTan_map φ rfl (hu.1 τ i).1, he τ i⟩, fun τ w hw hwe => ?_⟩
  have h3 := eig_of_full c (fun τ i => resM φ (v τ i)) (fun τ i => (eig_iff c τ _).1 (he τ i)) h2 τ (tanOf hw)
    ((eig_iff c τ _).1 hwe)
  exact (existsUnique_congr fun a => LieMet.isComb_iff (fun i => resM φ (v τ i)) a (tanOf hw)).2 h3
