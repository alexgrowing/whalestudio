import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeilChar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToOverSurjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEquivStdSymp
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateFreeOfCard
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.WeilIsGrpPullbackIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FlagComponentFramedPointFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.HtGen GlobalTheory.TrivFlag GlobalTheory.WholeFlag
open Formalism.MainNotions.DIV.Cons (intO)
open MonObj
open scoped TensorProduct NNReal
open GlobalTheory.HTLat GlobalTheory.ChTor

namespace GlobalTheory.HalfGeo.Iso

attribute [local instance] Over.cartesianMonoidalCategory

section Push

variable {C : Type} [Field C] {A : Over (Sp C)} [GrpObj A] {S₀ : Scheme.{0}} {G : Over S₀} [GrpObj G]
  {f : Sp C ⟶ S₀} {ψ : A.left ⟶ G.left}

theorem pow_eq_one_of_push (hpb : IsGrpPullback A G f ψ) {T₀ : Over S₀} (τ : Sp C ⟶ T₀.left) (hτ : τ ≫ T₀.hom = f)
    (a : Pts A) (w : T₀ ⟶ G) (hw : τ ≫ w.left = a.left ≫ ψ) {k : ℕ} (hk : w ^ k = 1) : a ^ k = 1 := by
  let T : Over (Sp C) := Over.mk (𝟙 (Sp C))
  have inj : ∀ {x y : T ⟶ A}, pushHom hpb T x = pushHom hpb T y → x = y := fun {x y} h =>
    Over.OverMorphism.ext (hpb.1.hom_ext (congrArg (fun q => q.left) h) (by rw [Over.w, Over.w]))
  let U : Over.mk (T.hom ≫ f) ⟶ T₀ := Over.homMk τ (hτ.trans (Category.id_comp f).symm)
  have hU : U ≫ w = pushHom hpb T a := Over.OverMorphism.ext hw
  apply inj
  rw [map_pow, map_one, ← hU, ← MonObj.comp_pow, hk, MonObj.comp_one]

omit [GrpObj A] [GrpObj G] in

theorem exists_lift (hpb : IsPullback ψ A.hom G.hom f) (s : Over.mk f ⟶ G) : ∃ a : Pts A, a.left ≫ ψ = s.left :=
  ⟨Over.homMk (hpb.lift s.left (𝟙 _) ((Over.w s).trans (Category.id_comp f).symm)) (hpb.lift_snd _ _ _),
    hpb.lift_fst _ _ _⟩

omit [GrpObj A] [GrpObj G] in

theorem exists_push (hpb : IsPullback ψ A.hom G.hom f) (a : Pts A) : ∃ s : Over.mk f ⟶ G, a.left ≫ ψ = s.left :=
  ⟨Over.homMk (a.left ≫ ψ) (by
    rw [Category.assoc, hpb.w, ← Category.assoc, Over.w a]
    exact Category.id_comp f), rfl⟩

end Push

theorem eq_weil {C : Type} [Field C] [IsAlgClosed C] [CharZero C] (A : Out.PolAV (Sp C)) {S₀ : Scheme.{0}} {G : Over S₀}
    [GrpObj G] {L : LB G.left} (hL₀ : L.IsLB) {f : Sp C ⟶ S₀} {ψ : A.A.left ⟶ G.left} (hpb : IsGrpPullback A.A G f ψ)
    (hL : LBIso A.L (L.pull ψ)) {k : ℕ} (hk : 1 ≤ k) {x y : Pts A.A} (hx : x ^ k = 1) (hy : y ^ k = 1)
    {x₀ y₀ : Over.mk f ⟶ G} (ex : x.left ≫ ψ = x₀.left) (ey : y.left ≫ ψ = y₀.left) {c : Cˣ}
    (hW : Out.WeilIs G L (k : ℤ) x₀ y₀ (unitOn c)) : c = weil A k x y := by
  have hLaws : Out.Laws := GlobalTheory.firstFiveLaws.1
  obtain ⟨r, hr, ⟨cu⟩⟩ := GlobalTheory.PolAV_exists_cubical hLaws.cube A
  obtain ⟨w, hw⟩ := hL
  have h := GlobalTheory.WeilCube.weilIs_pull cu hLaws.globalFns A.isAb hL₀ hpb w hw
    (T := Over.mk (𝟙 (Sp C))) (T₀ := Over.mk f) (𝟙 _) (by rw [Category.id_comp]; exact (Category.id_comp f).symm) hx hy
    (x₀ := x₀) (y₀ := y₀) (by simp [ex]) (by simp [ey]) hW
  have hu : ∀ u : Γ(Sp C, ⊤)ˣ, Units.map (Scheme.Hom.appTop (𝟙 (Sp C))).hom.toMonoidHom u = u := by
    intro u; ext; simp
  erw [hu] at h
  exact (GlobalTheory.HTLat.weilIs_iff hk hx hy c).1 h

theorem exists_unit_exp {p : ℕ} [Fact p.Prime] {C : Type} [Field C] (ε : Eps p C) {ζ : Cˣ}
    (hζ : IsPrimitiveRoot ζ (p ^ 2)) : ∃ u : ℤ_[p]ˣ, ∀ (a : ℤ_[p]) (b : ℤ), ε.1.lev 2 ^ GlobalTheory.PDiv.digit 2 a = ζ ^ b →
      (p : ℤ_[p]) ∣ a - u * (b : ℤ_[p]) := by
  have hp : p.Prime := Fact.out
  haveI : NeZero (p ^ 2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hε := ε.isPrimitiveRoot 2
  obtain ⟨i, -, rfl⟩ := hε.eq_pow_of_mem_rootsOfUnity ((mem_rootsOfUnity _ _).2 hζ.pow_eq_one)
  have hi : i.Coprime (p ^ 2) := (hε.pow_iff_coprime (pow_pos hp.pos 2) i).1 hζ
  have hi' : IsUnit (i : ℤ_[p]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact (Nat.Coprime.coprime_dvd_right (dvd_pow_self p two_ne_zero) hi).symm
  refine ⟨hi'.unit, fun a b hab => ?_⟩
  have h1 : ε.1.lev 2 ^ ((GlobalTheory.PDiv.digit 2 a : ℤ) - i * b) = 1 := by
    rw [zpow_sub, zpow_natCast, hab, zpow_mul, zpow_natCast, mul_inv_cancel]
  have h2 := (hε.zpow_eq_one_iff_dvd _).1 h1
  have h3 := map_dvd (Int.castRingHom ℤ_[p]) h2
  have h4 := GlobalTheory.PDiv.pow_dvd_sub_digit 2 a
  simp only [eq_intCast, Int.cast_natCast, Int.cast_sub, Int.cast_mul, Nat.cast_pow, Int.cast_pow] at h3
  have h5 := dvd_add h4 h3
  rw [sub_add_sub_cancel] at h5
  exact (dvd_pow_self _ two_ne_zero).trans h5

theorem norm_sub_lt {p : ℕ} [Fact p.Prime] {g : ℕ} (h k : Fin g → ↥(intO ℂ_[p])) (a : Fin g → ℂ_[p])
    (hp : ‖(p : ℂ_[p])‖ < 1) (ha : ∀ i, ‖(p : ℂ_[p]) * a i‖ ≤ 1)
    (hk : ∀ i, h i - k i ∈ Ideal.span {(p : ↥(intO ℂ_[p])) ^ 2}) :
    ‖∑ i, (h i : ℂ_[p]) * a i - ∑ i, a i * (k i : ℂ_[p])‖ < 1 := by
  rw [← Finset.sum_sub_distrib]
  refine lt_of_le_of_lt (IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => ?_) hp
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 (hk i)
  have hc' : (h i : ℂ_[p]) - k i = (p : ℂ_[p]) ^ 2 * c := by exact_mod_cast congrArg Subtype.val hc
  have e : (h i : ℂ_[p]) * a i - a i * k i = p * (c * (p * a i)) := by linear_combination a i * hc'
  rw [e, norm_mul, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (mul_le_one₀ c.2 (norm_nonneg _) (ha i))

theorem sub_al_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
    (t : SAB H X) {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C ℝ≥0}
    {O : Type} [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]
    [HenselianLocalRing O] [Algebra ℤ_[p] O] {Λ : Type} [CommRing Λ] [StarRing Λ] (P : Point p v O Λ) {z : Sp O ⟶ X}
    {π : P.G.left ⟶ t.G.left} (hπ : IsGrpPullback P.G t.G z π) {n : ℕ} (c : TorsChar t z (p ^ n)) (s : P.T)
    (hc : ∀ (w : Over.mk (spMap (algebraMap O O) ≫ z) ⟶ t.G) (a : Pts P.A.A), a ^ (p ^ n) = 1 → w ^ (p ^ n) = 1 →
      a.left ≫ P.gen ≫ π = spMap (algebraMap O C) ≫ w.left →
        algebraMap O C (c.χ O w : O) = (weil P.A (p ^ n) a (s.lev n) : C))
    {g : ℕ} {e : Fin g → (Sp (DualNumber O) ⟶ t.G.left)} (he : ∀ i, IsTanAtG t z (e i)) {h : Fin g → O}
    (hh : DlogIs t p n c e h) (i : Fin g) (x : ReciprocityTheory.ChartRestriction.G.Pdiv.LieG P.Gt) (hx : (P.lieCmp x).1.left ≫ π = e i) :
    h i - (P.al₀ s).1 x ∈ Ideal.span {(p : O) ^ n} := by
  classical
  let w : Over.mk (spMap (algebraMap O (DualNumber (O ⧸ Ideal.span {(p : O) ^ n}))) ≫ z) ⟶ t.G :=
    Over.homMk (spMap (dualMap (Ideal.Quotient.mk (Ideal.span {(p : O) ^ n}))) ≫ e i) (by
      rw [Category.assoc, (he i).1, ← Category.assoc, ← Spec.map_comp]
      congr 2
      ext r <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.algebraMap_eq_inl'])
  have h1 := hh _ _ (GlobalTheory.ShFam.isCombAtG_single t z he i) w rfl
  have h2 := GlobalTheory.TorsCharDlog.snd_chi_eq t P z π hπ n c s (fun w' y hw' hy => hc w' y
    (pow_eq_one_of_push (P.gen_pull.comp hπ) (T₀ := Over.mk (spMap (algebraMap O O) ≫ z))
      (spMap (algebraMap O C)) (by
        change _ ≫ _ ≫ z = _
        rw [← Category.assoc, ← Spec.map_comp]
        rfl) y w' hy.symm hw') hw' hy) x w (by rw [hx]; rfl)
  rw [← Ideal.Quotient.eq]
  simpa [Pi.single_apply] using h1.symm.trans h2

set_option maxHeartbeats 1000000 in

theorem isoSt_of : IntSt → LinSt → GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.HodgeTateKernelAtPoint → IsoSt := by
  intro hI hLin hK E _ _ _ H Dw l Xo c O _ β Z p _ z yy hP N hN s ζ B J hζ hBJ hG ch hch g e h he hh a a' ha ha' hb hb'
  classical
  obtain ⟨hu, hcomp, hhens, hint, ⟨io⟩⟩ := hI p
  haveI : Fact ¬IsUnit (p : ↥(intO ℂ_[p])) := ⟨hu⟩
  letI a1 : Algebra ℤ_[p] ↥(intO ℂ_[p]) := io.toAlgebra
  letI a2 : Algebra ℤ_[p] ℂ_[p] := ((algebraMap ↥(intO ℂ_[p]) ℂ_[p]).comp io).toAlgebra
  haveI a3 : @IsScalarTower ℤ_[p] ↥(intO ℂ_[p]) ℂ_[p] a1.toSMul Algebra.toSMul a2.toSMul :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨v, Λ, _, _, P, π, ψ, hπ, hψ, hsq, hL⟩ := hP
  have hk : 1 ≤ p ^ 2 := one_le_ppow p 2
  have hp1 : ‖(p : ℂ_[p])‖ < 1 := by
    by_contra hcon
    have h0 : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
    refine hu (IsUnit.of_mul_eq_one ⟨(p : ℂ_[p])⁻¹, ?_⟩ (Subtype.ext ?_))
    · change ‖(p : ℂ_[p])⁻¹‖ ≤ 1
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ (not_lt.1 hcon)
    · exact mul_inv_cancel₀ h0

  have hg : P.A.g = Module.finrank ℚ E / 2 * (Dw.p + Dw.q) := by
    have h1 := GlobalTheory.ObjDim.smoothOfRelativeDimension Z.oF
    have h2 : SmoothOfRelativeDimension (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) P.A.A.hom :=
      (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hψ.1 h1
    exact ReciprocityTheory.ChartRestriction.G.H1.dim_unique P.A.A.hom P.A.smoothDim h2
      ((η[P.A.A]).left (Nonempty.some (inferInstanceAs (Nonempty (Sp ℂ_[p])))))
  have hrk : Module.finrank ℤ_[p] P.T = N := by rw [P.hodgeTateLatticePoint_finrank_tateModule, hg, hN, GlobalTheory.ZM.finrank_int_lattice]

  have hlift : ∀ m, ∃ t : P.T, (Tate.lev t 2).left ≫ ψ = (s m).left := fun m => by
    obtain ⟨y, hy⟩ := exists_lift hψ.1 (s m)
    have hy1 := pow_eq_one_of_push hψ (T₀ := Over.mk yy) (𝟙 _) (Category.id_comp _) y (s m)
      ((Category.id_comp _).trans hy.symm) (hG.1 m)
    obtain ⟨t, ht⟩ := (tate_free_of_card p _ _ P.card_torsion).2.1 2 y hy1
    exact ⟨t, by rw [ht, hy]⟩
  choose t ht using hlift
  obtain ⟨u, hu'⟩ := exists_unit_exp P.eps hζ
  have hgram : ∀ m m', (p : ℤ_[p]) ∣ pairT P.A P.eps (t m) (t m') - u * (B m m' : ℤ_[p]) := fun m m' =>
    hu' _ _ ((pow_pairT P.A P.eps (t m) (t m') 2).trans (eq_weil P.A Z.oF.t.PP.isLB hψ hL hk (Tate.lev_pow _ 2)
      (Tate.lev_pow _ 2) (ht m) (ht m') (hG.2 m m')).symm)

  have hx : ∀ i, ∃ x : ReciprocityTheory.ChartRestriction.G.Pdiv.LieG P.Gt, (P.lieCmp x).1.left ≫ π = e i := fun i => by
    obtain ⟨y, hy⟩ := GlobalTheory.LocM.TanPair.exists_lieG hπ (he.1 i)
    obtain ⟨x, rfl⟩ := P.lieCmp.surjective y
    exact ⟨x, hy⟩
  choose x hx using hx
  have hd : ∀ m i, h m i - (P.al₀ (t m)).1 (x i) ∈ Ideal.span {(p : ↥(intO ℂ_[p])) ^ 2} := fun m i =>
    sub_al_mem Z.t P hπ (ch m) (t m) (fun w' y hy1 hw' hy => by
      obtain ⟨σ, hσ⟩ := exists_push hψ.1 y
      have h3 := hch m w' σ hw' (by rw [← hσ, Category.assoc, hsq]; exact hy)
      exact congrArg Units.val (eq_weil P.A Z.oF.t.PP.isLB hψ hL hk hy1 (Tate.lev_pow _ 2) hσ (ht m) h3))
      he.1 (hh m) i (x i) (hx i)

  obtain ⟨-, -, -, -, -, -, -, h5, -, h7⟩ := hK p ℂ_[p] v ↥(intO ℂ_[p]) Λ P
  have hW : ∀ a : Fin g → ℂ_[p], ∑ i, a i • P.bLie (x i) ∈ P.W := fun a => by
    rw [h7]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  have hval : ∀ (a : Fin g → ℂ_[p]) m, P.pairV (∑ i, a i • P.bLie (x i)) (1 ⊗ₜ t m) =
      ∑ i, a i * ((P.al₀ (t m)).1 (x i) : ℂ_[p]) := fun a m => by
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, P.pairV_bLie, smul_eq_mul]
    rfl
  refine hLin p (fun r => (io r).2) P.T N hrk (pairT P.A P.eps) t u B J hBJ hgram _ _ ((h5 _).1 (hW a) _ (hW a')) _ _ hb hb'
    (fun m => ?_) fun m => ?_
  · exact (congrArg (fun r => ‖_ - r‖) (hval a m)).trans_lt (norm_sub_lt _ _ a hp1 ha (hd m))
  · exact (congrArg (fun r => ‖_ - r‖) (hval a' m)).trans_lt (norm_sub_lt _ _ a' hp1 ha' (hd m))

end GlobalTheory.HalfGeo.Iso
