import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiInv
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RangeSubsetOfGeom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackTer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPullbackAbelianMapUniqueOfBaseEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPullbackCompFactorsStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiInverseIsogenyPairBaseChangeGrpPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiInverseIsogenySquareCompatCompQuasiInvStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelStableIffPulledBackIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorTypeIffPulledBackIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolKerAtPullbackOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrderActionDescentAlongIsogenyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieOfQuasiInverseIsogenyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizationDescentOfQuasiIsogeny
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiInverseRootBundleSymmetricStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiInverseRootBundleRosatiDescendedActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagRootPullbackQuasiInverseStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationDescentAlongQuasiIsogenyCompat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowPolarizationIsoPullbackOfDescent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationKernelOfPIsogenyQuasiInverse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsObjMapOfPIsogenyPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyRepresentableFiniteEtaleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClopenKernelStableHarrisTaylorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPullbackKernelLocusIsClopenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClopenLocusOfAnnihilator

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES.IsogRep

section
variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

theorem exists_comp {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R} {o₁ : Obj b N s₁}
    {o₂ : Obj b N s₂} {o₃ : Obj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃} (h₁ : ObjMap o₁ o₂ f) (h₂ : ObjMap o₂ o₃ g) :
    ∃ m : ObjMap o₁ o₃ (f ≫ g), m.φ = h₁.φ ≫ h₂.φ := by
  have sq : IsSquare (h₁.φ ≫ h₂.φ) (h₁.φ₂ ≫ h₂.φ₂) := by
    constructor
    · rw [Category.assoc, h₂.sq.1, ← Category.assoc, h₁.sq.1, Category.assoc]
    · rw [Category.assoc, h₂.sq.2, ← Category.assoc, h₁.sq.2, Category.assoc]
  have act : ∀ c, (o₁.act.act c).left ≫ (h₁.φ ≫ h₂.φ) = (h₁.φ ≫ h₂.φ) ≫ (o₃.act.act c).left := by
    intro c
    rw [← Category.assoc, h₁.act, Category.assoc, h₂.act, Category.assoc]
  have eta : ∀ y, (o₁.eta y).left ≫ (h₁.φ ≫ h₂.φ) = (f ≫ g) ≫ (o₃.eta y).left := by
    intro y
    rw [← Category.assoc, h₁.eta, Category.assoc, h₂.eta, Category.assoc]
  have H : LBIso (o₂.P.pull h₁.φ₂) ((o₃.P.pull h₂.φ₂).pull h₁.φ₂) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull o₂.P h₁.φ₂ h₁.φ₂ rfl)
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (o₃.P.pull h₂.φ₂) h₁.φ₂ h₁.φ₂ rfl) h₂.pol
  have H' : LBIso (o₂.P.pull h₁.φ₂) (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
    LBIso.chartPull (chartPullId _) (chartPullIn o₃.P (fun _ : PUnit => h₂.φ₂) (fun _ => 1) h₁.φ₂) H
  have pol : LBIso o₁.P (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
    LBIso.trans o₁.isLB (pull_isLB o₂.isLB _) (pull_isLB o₃.isLB _) h₁.pol H'
  exact ⟨⟨h₁.φ ≫ h₂.φ, h₁.φ₂ ≫ h₂.φ₂, h₁.cart.comp h₂.cart, sq, act, pol, eta⟩, rfl⟩

theorem exists_factor (hN : 3 ≤ N) (hNp : N.Coprime p) {S₀ S₁ T : Scheme.{0}} {s₀ : S₀ ⟶ Sp R} {s₁ : S₁ ⟶ Sp R}
    {t : T ⟶ Sp R} {o₀ : Obj b N s₀} {o₁ : Obj b N s₁} {o : Obj b N t} {g : S₁ ⟶ S₀} {h : T ⟶ S₁} {x : T ⟶ S₀}
    (e : h ≫ g = x) (m₁ : ObjMap o₁ o₀ g) (m : ObjMap o o₀ x) : ∃ m' : ObjMap o o₁ h, m'.φ ≫ m₁.φ = m.φ := by
  subst e
  obtain ⟨m'⟩ := GlobalTheory.T.harrisTaylorPullback_comp_factors p D R b N _ _ _ _ _ _ o₀ o₁ o g h m₁ m
  obtain ⟨n, hn⟩ := exists_comp m' m₁
  exact ⟨m', hn.symm.trans (GlobalTheory.T.harrisTaylor_pullback_abelian_map_unique_of_base_eq p D R b N hN hNp _ _ _ _ _ _ _ _ n m rfl)⟩

theorem exists_pull {S S' : Scheme.{0}} {s : S ⟶ Sp R} (f : S' ⟶ S) (o : Obj b N s) {s' : S' ⟶ Sp R}
    (e : f ≫ s = s') : ∃ o' : Obj b N s', Nonempty (ObjMap o' o f) := by
  subst e
  exact GlobalTheory.T.exists_harrisTaylorObject_pullback p D R b N S S' s f o

theorem isUnit_pow {S : Scheme.{0}} (s : S ⟶ Sp R) (hp : IsUnit ((p : ℕ) : R)) {c : ℕ} (hc : ∃ e : ℕ, c = p ^ e) :
    IsUnit (c : Γ(S, ⊤)) := by
  obtain ⟨e, rfl⟩ := hc
  have := (hp.pow e).map (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
  rwa [← Nat.cast_pow, map_natCast] at this

theorem exists_obj {c : ℕ} {Y : Scheme.{0}} [IsLocallyNoetherian Y] {s : Y ⟶ Sp R} (o : Obj b N s) (B : Over Y)
    [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A) (hp : IsUnit ((p : ℕ) : R)) (hc : ∃ e : ℕ, c = p ^ e)
    (hB : IsAbelianScheme B) (hq : IsQuasiInv c ψ ψ') (h1 : KerStableAt o ψ (𝟙 Y)) (h2 : PolKerAt o ψ' c (𝟙 Y)) :
    ∃ (o' : Obj b N s) (χ : o.A ⟶ o'.A) (θ : o'.A.left ⟶ B.left), IsPIsog c o o' χ ∧
      IsGrpPullback o'.A B (𝟙 Y) θ ∧ ψ.left = χ.left ≫ θ := by
  obtain ⟨act', hact⟩ := GlobalTheory.T.exists_orderAction_descent_along_isogeny p D R b N c Y s o B ψ ψ' hp hc hB hq h1
  obtain ⟨P', hP', w1, w2⟩ := GlobalTheory.T.exists_polarization_descent_of_quasi_isogeny p D R b N c Y s o B ψ ψ' hp hc hB hq h2
  have hlie := GlobalTheory.T.harrisTaylor_lie_of_quasiInverseIsogeny p D R b N c Y s o B ψ ψ' hp hc hB hq act' hact
  haveI := hq.1
  let o' : Obj b N s :=
    { A := B, ab := hB, act := act', P := P', isLB := hP'.1, rig₁ := hP'.2.1, rig₂ := hP'.2.2
      symm := GlobalTheory.T.quasiInverse_root_bundle_symmetric p D R b N c Y s o B ψ ψ' hp hc hB hq P' hP' w1 w2
      ample := GlobalTheory.T.relAmple_diag_root_pullback_quasiInverse p D R b N c Y s o B ψ ψ' hp hc hB hq P' hP' w1 w2
      kerP := GlobalTheory.T.polarization_descent_along_quasi_isogeny_compat p D R b N c Y s o B ψ ψ' hp hc hB hq h2 P' hP' w1 w2
      rosati := GlobalTheory.T.quasiInverse_root_bundle_rosati_descended_action p D R b N c Y s o B ψ ψ' hp hc hB hq P' hP' w1 w2 act' hact
      lie := hlie.1, lieRank := hlie.2
      eta := fun y => o.eta y ≫ ψ
      eta_add := fun x y => by rw [o.eta_add, MonObj.mul_comp]
      eta_lin := fun a x => by rw [o.eta_lin, Category.assoc, hact, Category.assoc]
      eta_ker := fun x => by rw [o.eta_ker, MonObj.one_comp]
      geom := GlobalTheory.T.pow_polarization_iso_pullback_of_descent p D R b N c Y s o B ψ ψ' hp hc hB hq P' hP' w1 w2 act' hact }
  exact ⟨o', ψ, 𝟙 _, ⟨hc, hq.1, hact, fun _ => rfl, ⟨w2⟩, ψ', hq.2.1, hq.2.2.1, hq.2.2.2⟩,
    GlobalTheory.SiegLower.isGrpPullback_id B, (Category.comp_id _).symm⟩

end

theorem exists_rep : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → IsUnit ((p : ℕ) : R) → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s), ∃ (Y : Over S) (o₀ : Obj b N (Y.hom ≫ s)) (m₀ : ObjMap o₀ o Y.hom) (o' : Obj b N (Y.hom ≫ s)) (ψ : o₀.A ⟶ o'.A), IsFinite Y.hom ∧ Etale Y.hom ∧ IsPIsog c o₀ o' ψ ∧ IsTj r w j o₀ o' ψ ∧ ∀ (T : Scheme.{0}) (x : T ⟶ S) (o₁ o₁' : Obj b N (x ≫ s)) (m : ObjMap o₁ o x) (ψ₁ : o₁.A ⟶ o₁'.A), IsPIsog c o₁ o₁' ψ₁ → IsTj r w j o₁ o₁' ψ₁ → ∃! y : T ⟶ Y.left, y ≫ Y.hom = x ∧ ∃ (m₀' : ObjMap o₁ o₀ y) (m₁ : ObjMap o₁' o' y), m₀'.φ ≫ ψ.left = ψ₁.left ≫ m₁.φ := by
  intro p _ D R _ _ b N hN hNp hp r w j c _ _ _ hc0 _ S _ s o
  have hc : ∃ e : ℕ, c = p ^ e := hc0.imp fun _ h => h.1
  have hcpos : 0 < c := by
    obtain ⟨e, rfl⟩ := hc
    exact pow_pos (Fact.out : p.Prime).pos e
  obtain ⟨Z, hZf, hZe, hZ⟩ := GlobalTheory.T.isogeny_representable_finite_etale S o.A c o.ab hcpos (isUnit_pow s hp hc)
  obtain ⟨oZ, ⟨mZ⟩⟩ := exists_pull Z.hom o rfl
  obtain ⟨B, _, _, ψ, ψ', hB, hq, huniv⟩ := hZ oZ.A mZ.φ mZ.cart
  obtain ⟨W₁, a₁, c₁, H₁⟩ := GlobalTheory.T.exists_clopen_kernelStable_harrisTaylor p D R b N c _ _ oZ B ψ ψ' hp hc hB hq
  obtain ⟨W₂, a₂, c₂, H₂⟩ := GlobalTheory.T.harrisTaylor_pullback_kernel_locus_isClopen p D R b N c _ _ oZ B ψ ψ' hp hc hB hq
  obtain ⟨W₃, a₃, c₃, H₃⟩ := GlobalTheory.T.exists_clopen_locus_of_annihilator p D R b N c _ _ oZ B ψ ψ' hp hc hB hq r w j
  haveI := hZf
  haveI := hZe
  obtain ⟨Y, i, hYf, hYe, hmono, Hi⟩ := GlobalTheory.LevCover.exists_sub (Z := Z)
    ⟨W₁ ∩ W₂ ∩ W₃, (a₁.inter a₂).inter a₃⟩ ((c₁.inter c₂).inter c₃)
  haveI := hYf
  haveI : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have hi : Set.range i.left.base ⊆ W₁ ∩ W₂ ∩ W₃ := (Hi Y i).2 ⟨𝟙 Y, Category.id_comp i⟩
  obtain ⟨o₀, ⟨mi⟩⟩ := exists_pull i.left oZ (s' := Y.hom ≫ s) (by rw [← Category.assoc, Over.w i])
  obtain ⟨m₀, hm₀⟩ : ∃ m₀ : ObjMap o₀ o Y.hom, m₀.φ = mi.φ ≫ mZ.φ := by
    have H : ∀ g, i.left ≫ Z.hom = g → ∃ m₀ : ObjMap o₀ o g, m₀.φ = mi.φ ≫ mZ.φ := by
      rintro _ rfl
      exact exists_comp mi mZ
    exact H _ (Over.w i)
  obtain ⟨B₀, _, _, θ₀, ψ₀, ψ₀', hB₀, hθ₀, hq₀, e₀, e₀'⟩ :=
    GlobalTheory.T.quasiInverseIsogenyPair_baseChange_grpPullback _ _ i.left oZ.A B c ψ ψ' o₀.A mi.φ hB hq mi.cart
  obtain ⟨o', χ, θ₁, hχ, hθ₁, e₁⟩ := exists_obj o₀ B₀ ψ₀ ψ₀' hp hc hB₀ hq₀
    ((GlobalTheory.T.kernelStable_iff_pulledBack_identity p D R b N _ _ _ _ _ o₀ oZ mi B₀ B θ₀ ψ₀ ψ hθ₀ e₀).1 ((H₁ _ _).1 fun z hz => (hi hz).1.1))
    ((GlobalTheory.T.polKerAt_pullback_of_isGrpPullback p D R b N _ _ _ _ _ o₀ oZ mi B₀ B θ₀ ψ₀' ψ' c hθ₀ e₀').1 ((H₂ _ _).1 fun z hz => (hi hz).1.2))
  have hθ : IsGrpPullback o'.A B i.left (θ₁ ≫ θ₀) := (hθ₁.comp hθ₀).congr (Category.id_comp _) rfl
  have eχ : mi.φ ≫ ψ.left = χ.left ≫ θ₁ ≫ θ₀ := by rw [e₀, e₁, Category.assoc]
  have htj : IsTj r w j o₀ o' χ := (tjAt_id_iff r w j o₀ o' χ).1
    ((GlobalTheory.T.harrisTaylorType_iff_pulledBack_identity p D R b N _ _ _ _ _ o₀ oZ mi o'.A B (θ₁ ≫ θ₀) χ ψ r w j hθ eχ).1
      ((H₃ _ _).1 fun z hz => (hi hz).2))
  refine ⟨Y, o₀, m₀, o', χ, hYf, hYe, hχ, htj, fun T x o₁ o₁' m ψ₁ h1 h2 => ?_⟩
  obtain ⟨ψ₁', hq₁⟩ := h1.exists_quasiInv
  obtain ⟨z, ⟨hz, θ, θ', eθ, hθa, hθb, eψ⟩, zu⟩ := huniv T x o₁.A m.φ o₁'.A ψ₁ ψ₁' m.cart o₁'.ab hq₁
  obtain ⟨mz, hmz⟩ := exists_factor hN hNp hz mZ m
  obtain rfl : θ = mz.φ := mZ.cart.1.hom_ext (eθ.trans hmz.symm) (hθa.1.w.trans mz.cart.1.w.symm)
  have eψ' := GlobalTheory.T.quasiInverseIsogeny_square_compat_comp_quasiInv _ _ z oZ.A B c ψ ψ' o₁.A o₁'.A mz.φ θ' ψ₁ ψ₁' o₁'.ab hcpos hq hq₁ mz.cart eψ
  have hr : Set.range z.base ⊆ W₁ ∩ W₂ ∩ W₃ := Set.subset_inter (Set.subset_inter
    ((H₁ _ z).2 ((GlobalTheory.T.kernelStable_iff_pulledBack_identity p D R b N _ _ _ _ _ o₁ oZ mz o₁'.A B θ' ψ₁ ψ hθb eψ).2 (h1.kerStableAt _)))
    ((H₂ _ z).2 ((GlobalTheory.T.polKerAt_pullback_of_isGrpPullback p D R b N _ _ _ _ _ o₁ oZ mz o₁'.A B θ' ψ₁' ψ' c hθb eψ').2
      (GlobalTheory.T.polarization_kernel_of_p_isogeny_quasi_inverse p D R b N c _ _ o₁ o₁' ψ₁ ψ₁' hp h1 hq₁))))
    ((H₃ _ z).2 ((GlobalTheory.T.harrisTaylorType_iff_pulledBack_identity p D R b N _ _ _ _ _ o₁ oZ mz o₁'.A B θ' ψ₁ ψ r w j hθb eψ).2
      ((tjAt_id_iff r w j o₁ o₁' ψ₁).2 h2)))
  obtain ⟨y, hy⟩ := (Hi (Over.mk x) (Over.homMk z hz)).1 hr
  have hyz : y.left ≫ i.left = z := congrArg CommaMorphism.left hy
  haveI : Mono i.left := inferInstanceAs (Mono ((Over.forget S).map i))
  refine ⟨y.left, ⟨Over.w y, ?_⟩, ?_⟩
  · obtain ⟨m₀', hm⟩ := exists_factor hN hNp hyz mi mz
    let φ₁ : o₁'.A.left ⟶ o'.A.left := hθ.1.lift θ' (o₁'.A.hom ≫ y.left) (by rw [hθb.1.w, Category.assoc, hyz])
    have f1 : φ₁ ≫ θ₁ ≫ θ₀ = θ' := hθ.1.lift_fst _ _ _
    have f2 : φ₁ ≫ o'.A.hom = o₁'.A.hom ≫ y.left := hθ.1.lift_snd _ _ _
    have hφ₁ : IsGrpPullback o₁'.A o'.A y.left φ₁ := hθ.cancel (hθb.congr hyz.symm f1.symm) f2
    have e : m₀'.φ ≫ χ.left = ψ₁.left ≫ φ₁ := by
      apply hθ.1.hom_ext
      · rw [Category.assoc, ← eχ, ← Category.assoc, hm, eψ, Category.assoc, f1]
      · rw [Category.assoc, Over.w χ, m₀'.cart.1.w, Category.assoc, f2, ← Category.assoc, Over.w ψ₁]
    obtain ⟨m₁, hm₁⟩ := GlobalTheory.T.exists_objMap_of_p_isogeny_pullback p D R b N c _ _ _ _ y.left o₁ o₁' o₀ o' m₀' ψ₁ χ φ₁ hp h1 hχ hφ₁ e
    exact ⟨m₀', m₁, by rw [hm₁, e]⟩
  · rintro y' ⟨hy', n₀, n₁, e⟩
    rw [← cancel_mono i.left, hyz]
    have hx : (y' ≫ i.left) ≫ Z.hom = x := by rw [Category.assoc, Over.w i, hy']
    obtain ⟨n, hn⟩ := exists_comp n₀ mi
    obtain ⟨n', hn'⟩ := exists_comp n mZ
    refine zu _ ⟨hx, n₀.φ ≫ mi.φ, n₁.φ ≫ θ₁ ≫ θ₀, ?_, n₀.cart.comp mi.cart, n₁.cart.comp hθ, ?_⟩
    · rw [← hn, ← hn']
      exact GlobalTheory.T.harrisTaylor_pullback_abelian_map_unique_of_base_eq p D R b N hN hNp _ _ _ _ _ _ _ _ n' m hx
    · rw [Category.assoc, eχ, ← Category.assoc, e, Category.assoc]

end GlobalTheory.UPel.HT.ES.IsogRep
