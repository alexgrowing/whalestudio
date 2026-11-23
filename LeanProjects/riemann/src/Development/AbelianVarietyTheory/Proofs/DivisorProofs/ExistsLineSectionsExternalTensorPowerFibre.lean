import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsIsKeyPow
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyUnitModels
open GlobalTheory.LocM (KeyAt)
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries
namespace GlobalTheory.BoxLine

theorem exists_isPullback_pow {S S' : Scheme.{0}} (g : S' ⟶ S) (G : Over S) (A B : Over S')
    (φ₀ : A.left ⟶ G.left) (h : IsPullback φ₀ A.hom G.hom g) (N : ℕ) (q : Fin N → (B ⟶ A))
    (hl : IsLimit (Fan.mk B q)) :
    ∃ φ : B.left ⟶ (pow G N).left, IsPullback φ B.hom (pow G N).hom g ∧
      ∀ k, φ ≫ pr G N k = (q k).left ≫ φ₀ := by
  let ψ : Over.mk (B.hom ≫ g) ⟶ pow G N := Pi.lift fun k =>
    Over.homMk ((q k).left ≫ φ₀) (by
      simp only [Over.mk_hom, Category.assoc]
      rw [h.w, ← Category.assoc, Over.w])
  have hψ : ∀ k, ψ.left ≫ pr G N k = (q k).left ≫ φ₀ := fun k => by
    have : ψ ≫ Pi.π (fun _ => G) k = _ := Pi.lift_π _ k
    exact congrArg (fun t => Over.Hom.left t) this
  have hw : ψ.left ≫ (pow G N).hom = B.hom ≫ g := Over.w ψ
  have hpr : ∀ k, pr G N k ≫ G.hom = (pow G N).hom := fun k => Over.w (Pi.π (fun _ => G) k)
  refine ⟨ψ.left, ⟨⟨hw⟩, ⟨?_⟩⟩, hψ⟩
  let c : ∀ s : PullbackCone (pow G N).hom g, Fin N → (Over.mk s.snd ⟶ A) := fun s k =>
    Over.homMk (h.lift (s.fst ≫ pr G N k) s.snd (by rw [Category.assoc, hpr, s.condition]))
      (h.lift_snd _ _ _)
  have hc : ∀ s k, (c s k).left ≫ φ₀ = s.fst ≫ pr G N k := fun s k => h.lift_fst _ _ _
  let m : ∀ s : PullbackCone (pow G N).hom g, Over.mk s.snd ⟶ B := fun s =>
    hl.lift (Fan.mk _ (c s))
  have hm : ∀ s k, (m s).left ≫ (q k).left = (c s k).left := fun s k =>
    congrArg (fun t => Over.Hom.left t) (hl.fac (Fan.mk _ (c s)) ⟨k⟩)
  refine PullbackCone.IsLimit.mk _ (fun s => (m s).left) ?_ ?_ ?_
  · intro s
    have hs : (m s).left ≫ B.hom = s.snd := Over.w (m s)
    let u : Over.mk (s.snd ≫ g) ⟶ pow G N := Over.homMk ((m s).left ≫ ψ.left) (by
      simp only [Over.mk_hom, Category.assoc]
      rw [hw, ← Category.assoc, hs])
    let v : Over.mk (s.snd ≫ g) ⟶ pow G N := Over.homMk s.fst s.condition
    have huv : u = v := by
      refine Pi.hom_ext _ _ fun k => ?_
      ext1
      change ((m s).left ≫ ψ.left) ≫ pr G N k = s.fst ≫ pr G N k
      rw [Category.assoc, hψ, ← Category.assoc, hm, hc]
    exact congrArg (fun t => Over.Hom.left t) huv
  · intro s
    exact Over.w (m s)
  · intro s t h1 h2
    let u : Over.mk s.snd ⟶ B := Over.homMk t h2
    have : u = m s := by
      refine hl.uniq (Fan.mk _ (c s)) u ?_
      rintro ⟨k⟩
      ext1
      change t ≫ (q k).left = (c s k).left
      refine h.hom_ext ?_ ?_
      · rw [hc, Category.assoc, ← hψ, ← Category.assoc, h1]
      · rw [Category.assoc, Over.w, h2]
        exact (Over.w (c s k)).symm
    exact congrArg (fun t => Over.Hom.left t) this

open GlobalTheory.CechPic in

theorem cls_pull_box {S : Scheme.{0}} (G : Over S) (L : LB G.left) (hL : L.IsLB) (N : ℕ)
    {X : Scheme.{0}} (φ : X ⟶ (pow G N).left) (h : ((boxLB G L N).pull φ).IsLB) :
    cls ((boxLB G L N).pull φ) h = ∑ k, pull (φ ≫ pr G N k) (cls L hL) := by
  rw [cls_pull (LB.isLB_linComb hL _ _), cls_linComb hL, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [one_smul, pull_comp]

theorem isLB_triv (X : Scheme.{0}) : (LB.triv X).IsLB :=
  ⟨by simp, fun _ => map_one _, fun _ _ _ => by simp⟩

open GlobalTheory.CechPic in

theorem sections_line : ∀ (V K : Type) [CommRing V] [Field K] (f : V →+* K) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (rig : LB.Gen (L.pull (eSec G))) (θ : L.Sec) (n : ℕ) (w : Fin n → (epsR V ⟶ G)) (x : KeyIn K), L.IsLB → IsFibreOf x G L rig θ w f → ∀ N : ℕ, ∃ (X' : Scheme.{0}) (p' : X' ⟶ Sp K) (φ : X' ⟶ (pow G N).left) (L' : LB X') (b : L'.Sec), IsPullback φ p' (pow G N).hom (spMap f) ∧ L'.IsLB ∧ LBIso L' ((boxLB G L N).pull φ) ∧ ∀ s : L'.Sec, ∃ a : K, ∀ i, s.f i = constFn p' _ a * b.f i := by
  intro V K _ _ f G _ _ L rig θ n w x hL hx N
  obtain ⟨φ₀, he, e, hg, F, hpb, hegen, -⟩ := hx
  have hbox : ∀ {X : Scheme.{0}} (φ : X ⟶ (pow G N).left), ((boxLB G L N).pull φ).IsLB :=
    fun φ => LB.isLB_linComb (LB.isLB_linComb hL _ _) _ _
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · obtain ⟨φ, hφ, -⟩ := exists_isPullback_pow (spMap f) G x.P.A (Over.mk (𝟙 (Sp K))) φ₀ hpb.1 0
      (fun k => k.elim0)
      (Fan.IsLimit.mk _ (fun s => Over.mkIdTerminal.from _) (fun _ k => k.elim0)
        (fun _ _ _ => Over.mkIdTerminal.hom_ext _ _))
    refine ⟨Sp K, 𝟙 _, φ, LB.triv _, ⟨fun _ => 1, fun _ _ => by simp⟩, hφ, isLB_triv _, ?_, ?_⟩
    · rw [iso_triv_iff, ← cls_eq_zero_iff (hbox φ), cls_pull_box G L hL]
      simp
    · intro s
      refine ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (s.f PUnit.unit), fun i => ?_⟩
      obtain rfl : i = PUnit.unit := rfl
      have h0 : ∀ (h : (⊤ : (Sp K).Opens) ≤ ⊤) (t : Γ(Sp K, ⊤)),
          ((Sp K).presheaf.map (homOfLE h).op).hom t = t := fun h t => by
        rw [show homOfLE h = 𝟙 _ from rfl, op_id, CategoryTheory.Functor.map_id]
        rfl
      simp [constFn, Scheme.Hom.appLE]
      exact (h0 _ _).symm
  · obtain ⟨y, p, -⟩ := GlobalTheory.KeyPow.exists_isKeyPow K x N hN
    obtain ⟨φ, hφ, hc⟩ := exists_isPullback_pow (spMap f) G x.P.A y.P.A φ₀ hpb.1 N p.pr p.lim
    obtain ⟨b, hb⟩ := principalPolarisation_exists_unique_section GlobalTheory.firstFiveLaws.2.1.secTwist y.P
    refine ⟨y.P.A.left, y.P.A.hom, φ, y.P.L, b, hφ, y.P.isLB, ?_, fun s => (hb s).exists⟩
    have h1 : cls x.P.L x.P.isLB = pull φ₀ (cls L hL) := by
      rw [← cls_pull hL φ₀ (LB.isLB_linComb hL _ _), cls_eq_iff]
      exact ⟨e, hegen⟩
    have h2 : cls y.P.L y.P.isLB
        = cls (Out.boxLB x.P.L p.pr) (LB.isLB_linComb x.P.isLB _ _) := by
      rw [cls_eq_iff]
      exact ⟨p.w, p.w_gen⟩
    rw [← cls_eq_iff y.P.isLB (hbox φ), cls_pull_box G L hL, h2, cls_linComb x.P.isLB]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [one_smul, hc, pull_comp, h1]

end GlobalTheory.BoxLine
