import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsHolomorphicUniformisationPowerThetaKeyDatu
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPolarisedAbelianSchemePower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TestObj

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PowFibre

section Pow

variable {S : Scheme.{0}} {G₀ G : Over S} [GrpObj G₀] [GrpObj G] {j : ℕ} (p : Out.IsPowGrp G₀ G j)

theorem over_ext {T : Over S} {a b : T ⟶ G₀} (h : ∀ i, a ≫ p.pr i = b ≫ p.pr i) : a = b :=
  p.lim.hom_ext fun ⟨i⟩ => h i

theorem left_ext {T : Scheme.{0}} {a b : T ⟶ G₀.left} (h₀ : a ≫ G₀.hom = b ≫ G₀.hom)
    (h : ∀ i, a ≫ (p.pr i).left = b ≫ (p.pr i).left) : a = b := by
  have := over_ext p (T := Over.mk (b ≫ G₀.hom)) (a := Over.homMk a h₀) (b := Over.homMk b rfl)
    fun i => Over.OverMorphism.ext (h i)
  exact congrArg (·.left) this

theorem exists_left_lift {T : Scheme.{0}} (s : T ⟶ S) (a : Fin j → (T ⟶ G.left)) (ha : ∀ i, a i ≫ G.hom = s) :
    ∃ x : T ⟶ G₀.left, x ≫ G₀.hom = s ∧ ∀ i, x ≫ (p.pr i).left = a i := by
  let c : Fan (fun _ : Fin j => G) := Fan.mk (Over.mk s) fun i => Over.homMk (a i) (ha i)
  exact ⟨(p.lim.lift c).left, Over.w (p.lim.lift c), fun i => congrArg (·.left) (p.lim.fac c ⟨i⟩)⟩

def incl (i : Fin j) : G ⟶ G₀ := p.lim.lift (Fan.mk _ fun i' => if i = i' then 𝟙 G else 1)

theorem incl_pr (i i' : Fin j) : incl p i ≫ p.pr i' = if i = i' then 𝟙 G else 1 :=
  p.lim.fac (Fan.mk _ fun i' => if i = i' then 𝟙 G else 1) ⟨i'⟩

theorem comp_incl_pr {T : Over S} (s : T ⟶ G) (i i' : Fin j) :
    (s ≫ incl p i) ≫ p.pr i' = if i = i' then s else 1 := by
  rw [Category.assoc, incl_pr]
  split_ifs
  exacts [Category.comp_id _, MonObj.comp_one _]

theorem unit_eq_one (G : Over S) [GrpObj G] : η[G] = (1 : 𝟙_ (Over S) ⟶ G) := by
  rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]

theorem unit_incl (i : Fin j) : η[G] ≫ incl p i = η[G₀] := by
  refine over_ext p fun i' => ?_
  have := p.hom i'
  rw [comp_incl_pr, IsMonHom.one_hom, unit_eq_one, ite_self]

theorem one_left (T G : Over S) [GrpObj G] : (1 : T ⟶ G).left = T.hom ≫ η[G].left := by
  rw [Hom.one_def, Over.comp_left]
  rfl

end Pow

theorem isTangent_incl {R : Type} [CommRing R] {G₀ G : Over (Sp R)} [GrpObj G₀] [GrpObj G] {j : ℕ}
    (p : Out.IsPowGrp G₀ G j) (i : Fin j) {v : epsR R ⟶ G} (hv : IsTangent v) : IsTangent (v ≫ incl p i) := by
  unfold IsTangent at hv ⊢
  rw [Over.comp_left, ← Category.assoc, hv, ← unit_incl p i]
  rfl

section Pull

variable {S S' : Scheme.{0}} {G₀ G : Over S} [GrpObj G₀] [GrpObj G] {G₀' G' : Over S'} [GrpObj G₀'] [GrpObj G']
  {j : ℕ} {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

theorem unit_pull (h : IsGrpPullback G' G f φ) : η[G'].left ≫ φ = f ≫ η[G].left := by
  have e := congrArg (fun z => z.left) (map_one (pushHom h (𝟙_ (Over S'))))
  rw [← unit_eq_one] at e
  refine e.trans ((one_left _ _).trans ?_)
  exact congrArg (· ≫ η[G].left) (Category.id_comp f)

theorem exists_pow_pullback (p : Out.IsPowGrp G₀ G j) (p' : Out.IsPowGrp G₀' G' j) (h : IsGrpPullback G' G f φ) :
    ∃ φ₀ : G₀'.left ⟶ G₀.left, IsGrpPullback G₀' G₀ f φ₀ ∧ ∀ i, φ₀ ≫ (p.pr i).left = (p'.pr i).left ≫ φ := by
  obtain ⟨φ₀, hw, hφ₀⟩ := exists_left_lift p (G₀'.hom ≫ f) (fun i => (p'.pr i).left ≫ φ) fun i => by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]
  refine ⟨φ₀, ⟨⟨⟨hw⟩, ⟨?_⟩⟩, fun T x y x₀ y₀ hx hy => ?_⟩, hφ₀⟩
  · have hs : ∀ (s : PullbackCone G₀.hom f) (i : Fin j), (s.fst ≫ (p.pr i).left) ≫ G.hom = s.snd ≫ f :=
      fun s i => by rw [Category.assoc, Over.w, s.condition]
    choose l hl₁ hl₂ using fun s : PullbackCone G₀.hom f =>
      exists_left_lift p' s.snd (fun i => h.1.lift _ _ (hs s i)) fun i => h.1.lift_snd _ _ _
    refine PullbackCone.IsLimit.mk _ l (fun s => left_ext p ?_ fun i => ?_) hl₁
      fun s m h₁ h₂ => left_ext p' (h₂.trans (hl₁ s).symm) fun i => ?_
    · rw [Category.assoc, hw, ← Category.assoc, hl₁, s.condition]
    · rw [Category.assoc, hφ₀, ← Category.assoc, hl₂, h.1.lift_fst]
    · rw [hl₂]
      refine h.1.hom_ext ?_ ?_
      · rw [h.1.lift_fst, Category.assoc, ← hφ₀, ← Category.assoc, h₁]
      · rw [h.1.lift_snd, Category.assoc, Over.w, h₂]
  · refine left_ext p ?_ fun i => ?_
    · rw [Over.w, Category.assoc, hw, ← Category.assoc, Over.w]
      rfl
    · have := p.hom i
      have := p'.hom i
      have e := h.2 T (x ≫ p'.pr i) (y ≫ p'.pr i) (x₀ ≫ p.pr i) (y₀ ≫ p.pr i)
        (by rw [Over.comp_left, Over.comp_left, hx, Category.assoc, Category.assoc, hφ₀])
        (by rw [Over.comp_left, Over.comp_left, hy, Category.assoc, Category.assoc, hφ₀])
      rw [← MonObj.mul_comp, ← MonObj.mul_comp, Over.comp_left, Over.comp_left] at e
      rw [e, Category.assoc, Category.assoc, hφ₀]

theorem incl_pull (p : Out.IsPowGrp G₀ G j) (p' : Out.IsPowGrp G₀' G' j) (h : IsGrpPullback G' G f φ)
    {φ₀ : G₀'.left ⟶ G₀.left} (hw : φ₀ ≫ G₀.hom = G₀'.hom ≫ f)
    (hφ₀ : ∀ i, φ₀ ≫ (p.pr i).left = (p'.pr i).left ≫ φ) (i : Fin j) :
    (incl p' i).left ≫ φ₀ = φ ≫ (incl p i).left := by
  refine left_ext p ?_ fun i' => ?_
  · rw [Category.assoc, hw, ← Category.assoc, Over.w, Category.assoc, Over.w, h.1.w]
  · rw [Category.assoc, hφ₀, ← Category.assoc, Category.assoc φ, ← Over.comp_left, ← Over.comp_left, incl_pr, incl_pr]
    split_ifs
    · simp
    · rw [one_left, one_left, Category.assoc, unit_pull h, ← Category.assoc, ← h.1.w, Category.assoc]

end Pull

open PowUnif in

theorem exists_powUnif_triv {G' G : Over (Sp ℂ)} [GrpObj G'] [GrpObj G] {j : ℕ} (p : Out.IsPowGrp G' G j)
    {L : LB G.left} {g : ℕ} (u : HolUnif G L g) {n : ℕ} (e : Fin j × Fin g ≃ Fin n) :
    ∃ u' : HolUnif G' (Test.trivLB G'.left) n, (∀ z, z ∈ u'.Λ ↔ ∀ i, blockPr e i z ∈ u.Λ) ∧
      ∀ z i, u'.ex z ≫ p.pr i = u.ex (blockPr e i z) := by
  let ex : (Fin n → ℂ) → (𝟙_ (Over (Sp ℂ)) ⟶ G') := fun z => powLift p fun i => u.ex (blockPr e i z)
  have hex : ∀ z i, ex z ≫ p.pr i = u.ex (blockPr e i z) := fun z i => powLift_pr p _ i
  let c : (Fin n → ℂ) → (Sp ℂ ⟶ G'.left) := fun z => (ex z).left
  let d : (Fin g → ℂ) → (Sp ℂ ⟶ G.left) := fun z => (u.ex z).left
  have hd : IsHolFamily d := u.hol
  have hc : IsHolFamily c := isHolFamily_pow p ex fun i => by
    simp only [hex]
    exact hd.precomp (blockPr e i).differentiable
  have := u.discrete
  refine ⟨⟨ex, fun z z' => pow_hom_ext p fun i => ?_, fun a => ?_, blockLat e u.Λ, fun z => ?_,
    blockLat_discrete e u.Λ, blockLat_full e u.Λ u.full, hc, fun _ _ => 1, fun _ => differentiableOn_const _,
    fun _ _ _ => one_ne_zero, fun a b z hz => ?_⟩, fun z => Iff.rfl, hex⟩
  · have := p.hom i
    rw [MonObj.mul_comp, hex, hex, hex, map_add, u.ex_add]
  · choose z hz using fun i => u.ex_onto (a ≫ p.pr i)
    refine ⟨∑ i, blockIn e i (z i), pow_hom_ext p fun i => ?_⟩
    rw [hex, ← hz, map_sum]
    simp only [blockPr_blockIn, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · constructor
    · intro h i
      have := p.hom i
      rw [← u.ker, ← hex, h, MonObj.one_comp]
    · intro h
      refine pow_hom_ext p fun i => ?_
      have := p.hom i
      rw [hex, MonObj.one_comp, (u.ker _).2 (h i)]
  · rw [_root_.mul_one]
    exact (valAt'_one (c z) hz).symm

open PowUnif in

theorem exists_pow : ∀ (R : Type) [CommRing R] (σ : R →+* ℂ) (P : Out.PolAV (Sp R)) (A' : Over (Sp ℂ)) [GrpObj A']
    (φ' : A'.left ⟶ P.A.left) (L' : LB A'.left) (u : HolUnif A' L' 1) (v : epsR R ⟶ P.A) (v' : epsR ℂ ⟶ A') (t : ℂ)
    (S : Set ℂ), IsAbelianScheme A' → SmoothOfRelativeDimension 1 A'.hom → IsGrpPullback A' P.A (spMap σ) φ' →
    (∀ w, w ∈ u.Λ ↔ w 0 ∈ S) → IsTangent v → IsTangent v' → v'.left ≫ φ' = spMap (Chart.dualMapR σ) ≫ v.left →
    u.IsDiff (fun _ ↦ t) v' → ∀ (g : ℕ) (j₀ : Fin g),
    ∃ (P₀ : Out.PolAV (Sp R)) (A₀ : Over (Sp ℂ)) (_ : GrpObj A₀) (φ₀ : A₀.left ⟶ P₀.A.left) (L₀ : LB A₀.left)
      (u₀ : HolUnif A₀ L₀ g) (v₀ : epsR R ⟶ P₀.A) (v₀' : epsR ℂ ⟶ A₀),
      IsAbelianScheme A₀ ∧ SmoothOfRelativeDimension g A₀.hom ∧ IsGrpPullback A₀ P₀.A (spMap σ) φ₀ ∧
      (∀ w, w ∈ u₀.Λ ↔ ∀ j, w j ∈ S) ∧ IsTangent v₀ ∧ IsTangent v₀' ∧
      v₀'.left ≫ φ₀ = spMap (Chart.dualMapR σ) ≫ v₀.left ∧ u₀.IsDiff (Pi.single j₀ t) v₀' := by
  intro R _ σ P A' _ φ' L' u v v' t S hA hsm hpb hΛ hv hv' hvv hdiff g j₀
  obtain ⟨P₀, p, -⟩ := GlobalTheory.CM.exists_polAV_isPowGrp R P g
  let p' := Out.powIsPowGrp A' g
  obtain ⟨φ₀, hφ₀, hpr⟩ := exists_pow_pullback p p' hpb
  let e : Fin g × Fin 1 ≃ Fin g := Equiv.prodUnique _ _
  obtain ⟨u₀, hΛ₀, hex⟩ := exists_powUnif_triv p' u e
  have hpow := PowGrp.powers _ _ _ g p'
  refine ⟨P₀, Out.powObj A' g, inferInstance, φ₀, _, u₀, v ≫ incl p j₀, v' ≫ incl p' j₀, hpow.2.2.2.1 hA,
    by simpa only [Nat.mul_one] using hpow.2.2.1 1 hsm, hφ₀, fun w => ?_, isTangent_incl p j₀ hv,
    isTangent_incl p' j₀ hv', ?_, ?_⟩
  · rw [hΛ₀]
    exact forall_congr' fun i => hΛ _
  · rw [Over.comp_left, Over.comp_left, Category.assoc, incl_pull p p' hpb hφ₀.1.w hpr, ← Category.assoc, hvv,
      Category.assoc]
  · have hT : ∀ z, u₀.ex (blockIn e j₀ z) = u.ex z ≫ incl p' j₀ := fun z => pow_hom_ext p' fun i' => by
      rw [hex, blockPr_blockIn, comp_incl_pr]
      split_ifs
      exacts [rfl, ex_zero u]
    have h := isDiff_map u u₀ (incl p' j₀) (blockIn e j₀) hT (isTangent_incl p' j₀ hv') hdiff
    have h₁ : blockIn e j₀ (fun _ => t) = Pi.single j₀ t := by
      rw [blockIn_apply]
      funext q
      simp only [Pi.single_apply, eq_comm (a := q)]
      rfl
    rwa [h₁] at h

end GlobalTheory.PowFibre

end
