import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsClasses
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairPtsEqSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovFn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetIdlVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepLatticeStabilizerVacuumEqDetCharSmul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmSplitHalves
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsLocalVacuumOfIsLatticeVacuumCoprimeLevel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InLatticeStabilizerAtPlaceOfSupportedStabilizer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvalVCutIdemOfNotMem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.RowVacScalar

noncomputable section

namespace GlobalTheory.LatStabScalar

open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter

variable {D : D7}

theorem mt_mul (V : HSp D) (a b : GA D V) : Formalism.L2.Theta.mt V (a * b) = Formalism.L2.Theta.mt V a * Formalism.L2.Theta.mt V b := by
  unfold Formalism.L2.Theta.mt
  rw [map_mul, Units.val_mul]

theorem mt_one (V : HSp D) : Formalism.L2.Theta.mt V 1 = 1 := by
  simp [Formalism.L2.Theta.mt]

theorem keeps_of_fwd {V : HSp D} {L : Set (Fin V.rank → D.host.E)} {g : GA D V}
    (h1 : ∀ y ∈ latHat D.host.F D.host.E L, ((Formalism.L2.Theta.mt V g).map (finPart D)).mulVec y ∈ latHat D.host.F D.host.E L)
    (h2 : ∀ y ∈ latHat D.host.F D.host.E L,
      ((Formalism.L2.Theta.mt V g⁻¹).map (finPart D)).mulVec y ∈ latHat D.host.F D.host.E L) :
    ∀ y, y ∈ latHat D.host.F D.host.E L ↔ ((Formalism.L2.Theta.mt V g).map (finPart D)).mulVec y ∈ latHat D.host.F D.host.E L := by
  intro y
  refine ⟨h1 y, fun hy => ?_⟩
  have := h2 _ hy
  rwa [Matrix.mulVec_mulVec, ← Matrix.map_mul, ← mt_mul, inv_mul_cancel, mt_one,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec] at this

theorem keeps_inv {V : HSp D} {L : Set (Fin V.rank → D.host.E)} {g : GA D V}
    (h : ∀ y, y ∈ latHat D.host.F D.host.E L ↔ ((Formalism.L2.Theta.mt V g).map (finPart D)).mulVec y ∈ latHat D.host.F D.host.E L) :
    ∀ y, y ∈ latHat D.host.F D.host.E L ↔
      ((Formalism.L2.Theta.mt V g⁻¹).map (finPart D)).mulVec y ∈ latHat D.host.F D.host.E L :=
  keeps_of_fwd (GlobalTheory.LocalLatStab.inv_keeps V L g h) (by rw [inv_inv]; exact fun y hy => (h y).1 hy)

theorem keeps_mul {V : HSp D} {L : Set (Fin V.rank → D.host.E)} {a b : GA D V}
    (ha : ∀ y, y ∈ latHat D.host.F D.host.E L ↔ ((Formalism.L2.Theta.mt V a).map (finPart D)).mulVec y ∈ latHat D.host.F D.host.E L)
    (hb : ∀ y, y ∈ latHat D.host.F D.host.E L ↔ ((Formalism.L2.Theta.mt V b).map (finPart D)).mulVec y ∈ latHat D.host.F D.host.E L) :
    ∀ y, y ∈ latHat D.host.F D.host.E L ↔
      ((Formalism.L2.Theta.mt V (a * b)).map (finPart D)).mulVec y ∈ latHat D.host.F D.host.E L := by
  refine keeps_of_fwd (fun y hy => ?_) (fun y hy => ?_)
  · rw [mt_mul, Matrix.map_mul, ← Matrix.mulVec_mulVec]
    exact (ha _).1 ((hb y).1 hy)
  · rw [mul_inv_rev, mt_mul, Matrix.map_mul, ← Matrix.mulVec_mulVec]
    exact (keeps_inv hb _).1 ((keeps_inv ha y).1 hy)

theorem hom_one_apply {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {n : ℕ} (i j : Fin n) :
    φ ((1 : Matrix (Fin n) (Fin n) R) i j) = (1 : Matrix (Fin n) (Fin n) R') i j := by
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs
  · exact map_one φ
  · exact map_zero φ

theorem hom_entry {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (t m o : R) :
    φ (t * m + (o - t * o)) = φ t * φ m + (φ o - φ t * φ o) := by
  rw [map_add, map_sub, map_mul, map_mul]

theorem hom_entry_zero {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {t : R} (ht : φ t = 0) (m o : R) :
    φ (t * m + (o - t * o)) = φ o := by
  rw [hom_entry, ht]; ring

theorem mulVec_comb {R : Type} [CommRing R] {n : ℕ} (t : R) (A : Matrix (Fin n) (Fin n) R) (y : Fin n → R) :
    (Matrix.of fun i j => t * A i j + ((1 : Matrix (Fin n) (Fin n) R) i j - t * (1 : Matrix (Fin n) (Fin n) R) i j)).mulVec y =
      t • A.mulVec y + (y - t • y) := by
  have : (Matrix.of fun i j => t * A i j + ((1 : Matrix (Fin n) (Fin n) R) i j - t * (1 : Matrix (Fin n) (Fin n) R) i j)) =
      t • A + (1 - t • (1 : Matrix (Fin n) (Fin n) R)) := by
    ext i j; simp
  rw [this, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec]

theorem exists_int_of_placeIdem {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) :
    ∃ α ∈ intAf D.host.F, finPart D (algebraMap (AF D.host.F) (AE D) ε) = α ⊗ₜ[D.host.F] (1 : D.host.E) := by
  obtain ⟨α, rfl, h1, h0⟩ := hε
  refine ⟨α, fun w => ?_, rfl⟩
  by_cases hw : w = v
  · subst hw; rw [h1]; exact one_mem _
  · rw [h0 w hw]; exact zero_mem _

theorem fwd_locPart {V : HSp D} {L : Set (Fin V.rank → D.host.E)} {g : GA D V} (v : HeightOneSpectrum (𝓞 D.host.F))
    (h : ∀ y ∈ latHat D.host.F D.host.E L, ((Formalism.L2.Theta.mt V g).map (finPart D)).mulVec y ∈ latHat D.host.F D.host.E L) :
    ∀ y ∈ latHat D.host.F D.host.E L,
      ((Formalism.L2.Theta.mt V (GlobalTheory.VacStab.locPart V v g)).map (finPart D)).mulVec y ∈ latHat D.host.F D.host.E L := by
  intro y hy
  obtain ⟨ε, hε⟩ : ∃ ε, IsPlaceIdem D v ε :=
    ⟨_, singleV D.host.F v 1, rfl, GlobalTheory.KStabBridge.evalV_sv_same v, fun _ hw => GlobalTheory.KStabBridge.evalV_sv_ne hw⟩
  obtain ⟨α, hα, ht⟩ := exists_int_of_placeIdem hε
  have hM : (Formalism.L2.Theta.mt V (GlobalTheory.VacStab.locPart V v g)).map (finPart D) =
      Matrix.of fun i j => (α ⊗ₜ[D.host.F] (1 : D.host.E)) * (Formalism.L2.Theta.mt V g).map (finPart D) i j +
        ((1 : Matrix (Fin V.rank) (Fin V.rank) _) i j - (α ⊗ₜ[D.host.F] (1 : D.host.E)) *
          (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j) := by
    ext i j
    rw [Matrix.map_apply, GlobalTheory.VacStab.mt_locPart V hε g]
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    rw [hom_entry, ht, hom_one_apply, Matrix.of_apply, Matrix.map_apply]
  rw [hM, mulVec_comb]
  exact add_mem (GlobalTheory.KStabBridge.latHat_smul L hα (h y hy)) (sub_mem hy (GlobalTheory.KStabBridge.latHat_smul L hα hy))

theorem inStabAt_locPart {V : HSp D} {L : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {g : GA D V}
    (hg : ∀ y, y ∈ latHat D.host.F D.host.E (L : Set (Fin V.rank → D.host.E)) ↔
      ((Formalism.L2.Theta.mt V g).map (finPart D)).mulVec y ∈ latHat D.host.F D.host.E (L : Set (Fin V.rank → D.host.E)))
    (v : HeightOneSpectrum (𝓞 D.host.F)) : InStabAt V L v (GlobalTheory.VacStab.locPart V v g) := by
  obtain ⟨ε, hε⟩ : ∃ ε, IsPlaceIdem D v ε :=
    ⟨_, singleV D.host.F v 1, rfl, GlobalTheory.KStabBridge.evalV_sv_same v, fun _ hw => GlobalTheory.KStabBridge.evalV_sv_ne hw⟩
  obtain ⟨hi, -, h0⟩ := GlobalTheory.VacStabFixed.place_comp hε
  have hm := GlobalTheory.VacStab.mt_locPart V hε g
  refine ⟨?_, fun w hw => ?_, keeps_of_fwd (fwd_locPart v fun y hy => (hg y).1 hy) ?_⟩
  · ext i j
    rw [Matrix.map_apply, hm]
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    rw [hom_entry_zero _ hi, hom_one_apply]
  · ext i j
    rw [Matrix.map_apply, Matrix.map_apply, hm]
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    have h0' := h0 w hw
    exact (hom_entry_zero ((compFin D w).comp (finPart D)) (t := algebraMap (AF D.host.F) (AE D) ε) h0' _ _).trans
      (hom_one_apply _ i j)
  · rw [← map_inv]
    exact fwd_locPart v fun y hy => (keeps_inv hg y).1 hy

theorem locPart_mem {V : HSp D} (v : HeightOneSpectrum (𝓞 D.host.F)) (g : GA D V) : GlobalTheory.VacStab.locPart V v g ∈ GfC V := by
  have h : GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v (GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v g) ∈
      (GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v).range := MonoidHom.mem_range.2 ⟨_, rfl⟩
  rw [GlobalTheory.AdelicU.range_emb] at h
  exact (GlobalTheory.AdelicU.mem_atPts.1 h).1

theorem locPart_locPart_ne {V : HSp D} {u v : HeightOneSpectrum (𝓞 D.host.F)} (h : u ≠ v) (g : GA D V) :
    GlobalTheory.VacStab.locPart V u (GlobalTheory.VacStab.locPart V v g) = 1 := by
  simp only [GlobalTheory.VacStab.locPart, MonoidHom.comp_apply]
  rw [GlobalTheory.AdelicU.proj_emb_ne _ _ h, map_one]

theorem locPart_locPart_self {V : HSp D} (v : HeightOneSpectrum (𝓞 D.host.F)) (g : GA D V) :
    GlobalTheory.VacStab.locPart V v (GlobalTheory.VacStab.locPart V v g) = GlobalTheory.VacStab.locPart V v g := by
  simp only [GlobalTheory.VacStab.locPart, MonoidHom.comp_apply]
  rw [GlobalTheory.AdelicU.proj_emb_self]

theorem idem_mul_det {R : Type} [CommRing R] {n : ℕ} (e : R) (X Y : Matrix (Fin n) (Fin n) R)
    (h : ∀ i j, e * X i j = e * Y i j) : e * X.det = e * Y.det := by
  have key : ∀ (s : Finset (Fin n)) (a b : Fin n → R), (∀ i, e * a i = e * b i) →
      e * ∏ i ∈ s, a i = e * ∏ i ∈ s, b i := by
    intro s a b hab
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi]
      calc e * (a i * ∏ j ∈ s, a j) = (e * a i) * ∏ j ∈ s, a j := by ring
        _ = b i * (e * ∏ j ∈ s, a j) := by rw [hab]; ring
        _ = e * (b i * ∏ j ∈ s, b j) := by rw [ih]; ring
  rw [Matrix.det_apply, Matrix.det_apply, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [mul_smul_comm, mul_smul_comm, key Finset.univ _ _ fun i => h (σ i) i]

theorem detIdl_locPart {e : AE D} (he : e * e = e) {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F}
    (hε : IsPlaceIdem D v ε) (hs : algebraMap (AF D.host.F) (AE D) ε * e = e) (V : HSp D) (g : GA D V) :
    GlobalTheory.RowVacScalar.detIdl e V (GlobalTheory.VacStab.locPart V v g) = GlobalTheory.RowVacScalar.detIdl e V g := by
  refine Units.ext ?_
  rw [GlobalTheory.RowVacScalar.detIdl_val he, GlobalTheory.RowVacScalar.detIdl_val he, idem_mul_det e _ _ fun i j => ?_]
  rw [GlobalTheory.VacStab.mt_locPart V hε g]
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  linear_combination (Formalism.L2.Theta.mt V g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) * hs

end GlobalTheory.LatStabScalar

namespace GlobalTheory.LatStabScalar

open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter

variable {D : D7}

theorem om_fixed {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om)
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hΛS : IsSelfDualC S ΛS) (hΛT : IsSelfDualC T ΛT) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (hvac : IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
      fun _ => True) f)
    {g : GA D S} (hg : g ∈ GfC S)
    (hgk : ∀ y, y ∈ latHat D.host.F D.host.E (ΛS : Set (Fin S.rank → D.host.E)) ↔
      ((Formalism.L2.Theta.mt S g).map (finPart D)).mulVec y ∈ latHat D.host.F D.host.E (ΛS : Set (Fin S.rank → D.host.E)))
    {h : GA D T} (hh : h ∈ GfC T)
    (hhk : ∀ y, y ∈ latHat D.host.F D.host.E (ΛT : Set (Fin T.rank → D.host.E)) ↔
      ((Formalism.L2.Theta.mt T h).map (finPart D)).mulVec y ∈ latHat D.host.F D.host.E (ΛT : Set (Fin T.rank → D.host.E)))
    (H : ∀ v, (CharUnramAt D χS v ∧ CharUnramAt D χT v) ∨
      (GlobalTheory.VacStab.locPart S v g = 1 ∧ GlobalTheory.VacStab.locPart T v h = 1)) :
    om (g, h) f = f := by
  have hm : ∀ (p q : GA D S × GA D T), om (p * q) f = om p (om q f) := fun p q => by
    rw [map_mul, Module.End.mul_apply]
  have ho : om 1 f = f := by rw [map_one, Module.End.one_apply]
  have hcont : ∀ w, Continuous fun p : GA D S × GA D T => om p f w := hW.om_cont f hf
  let K : Subgroup (GA D S × GA D T) :=
    { carrier := {p | om p f = f}
      one_mem' := ho
      mul_mem' := fun {a b} (ha : om a f = f) (hb : om b f = f) => by
        change om (a * b) f = f
        rw [hm, hb, ha]
      inv_mem' := fun {a} (ha : om a f = f) => by
        change om a⁻¹ f = f
        conv_lhs => rw [← ha]
        rw [← hm, inv_mul_cancel, ho] }
  have hK : ∀ p, p ∈ K ↔ om p f = f := fun p => Iff.rfl
  have hKc : IsClosed {p : GA D S × GA D T | om p f = f} :=
    isClosed_eq (continuous_pi hcont) continuous_const
  let KS : Subgroup (GA D S) := K.comap (MonoidHom.inl _ _)
  let KT : Subgroup (GA D T) := K.comap (MonoidHom.inr _ _)
  have hKS : IsClosed (KS : Set (GA D S)) := hKc.preimage (Continuous.prodMk_left 1)
  have hKT : IsClosed (KT : Set (GA D T)) := hKc.preimage (Continuous.prodMk_right 1)
  have h1 : g ∈ KS := GlobalTheory.LevelClosure.mem_of_isClosed D.sp.cm.sig S.gram hKS hg fun v => by
    change om (GlobalTheory.VacStab.locPart S v g, 1) f = f
    rcases H v with ⟨u1, u2⟩ | ⟨e1, -⟩
    · exact GlobalTheory.VacStabFixed.vacFixedAt D v ψ S T χS χT om hW u1 u2 ΛS ΛT hΛS hΛT f hf (isLatVac_at_of_all hvac v) _ 1
        (inStabAt_locPart hgk v) (inStabAt_one T ΛT v)
    · rw [e1, Prod.mk_one_one, ho]
  have h2 : h ∈ KT := GlobalTheory.LevelClosure.mem_of_isClosed D.sp.cm.sig T.gram hKT hh fun v => by
    change om (1, GlobalTheory.VacStab.locPart T v h) f = f
    rcases H v with ⟨u1, u2⟩ | ⟨-, e2⟩
    · exact GlobalTheory.VacStabFixed.vacFixedAt D v ψ S T χS χT om hW u1 u2 ΛS ΛT hΛS hΛT f hf (isLatVac_at_of_all hvac v) 1 _
        (inStabAt_one S ΛS v) (inStabAt_locPart hhk v)
    · rw [e2, Prod.mk_one_one, ho]
  have e : (g, h) = (g, 1) * (1, h) := by rw [Prod.mk_mul_mk, mul_one, one_mul]
  rw [e, hm]
  have h2' : om (1, h) f = f := h2
  have h1' : om (g, 1) f = f := h1
  rw [h2', h1']

end GlobalTheory.LatStabScalar

namespace GlobalTheory.LatStabScalar

open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter

variable {D : D7}

theorem pair_split {G H M : Type} [Group G] [Group H] [Monoid M] (φ : G × H →* M) (g a : G) (h b : H) :
    φ (g, h) = φ (a, b) * φ (a⁻¹ * g, b⁻¹ * h) := by
  rw [← map_mul, Prod.mk_mul_mk, mul_inv_cancel_left, mul_inv_cancel_left]

theorem om_locPart_pair {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om)
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hΛS : IsSelfDualC S ΛS) (hΛT : IsSelfDualC T ΛT) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (hvac : IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
      fun _ => True) f) {w : Pl D.host.E} (hw : Formalism.L2.NTheta.IsIdemAt (GlobalTheory.RowVacScalar.idemAt w) w)
    {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε)
    (hb : GlobalTheory.RowVacScalar.idemAt w + cA D (GlobalTheory.RowVacScalar.idemAt w) = algebraMap (AF D.host.F) (AE D) ε)
    {g : GA D S}
    (hgk : ∀ y, y ∈ latHat D.host.F D.host.E (ΛS : Set (Fin S.rank → D.host.E)) ↔
      ((Formalism.L2.Theta.mt S g).map (finPart D)).mulVec y ∈ latHat D.host.F D.host.E (ΛS : Set (Fin S.rank → D.host.E)))
    {h : GA D T}
    (hhk : ∀ y, y ∈ latHat D.host.F D.host.E (ΛT : Set (Fin T.rank → D.host.E)) ↔
      ((Formalism.L2.Theta.mt T h).map (finPart D)).mulVec y ∈ latHat D.host.F D.host.E (ΛT : Set (Fin T.rank → D.host.E))) :
    om (GlobalTheory.VacStab.locPart S v g, GlobalTheory.VacStab.locPart T v h) f =
      ((splitFacO χS χT (GlobalTheory.RowVacScalar.detIdl (GlobalTheory.RowVacScalar.idemAt w) S g)
        (GlobalTheory.RowVacScalar.detIdl (GlobalTheory.RowVacScalar.idemAt w) T h) : Circle) : ℂ) • f := by
  have he := hw.1
  have s1 : algebraMap (AF D.host.F) (AE D) ε * GlobalTheory.RowVacScalar.idemAt w = GlobalTheory.RowVacScalar.idemAt w := by
    rw [← hb]; linear_combination he.1 + he.2.1
  have ka := (inStabAt_locPart (L := ΛS) hgk v).2.2
  have kb := (inStabAt_locPart (L := ΛT) hhk v).2.2
  have hx : IsDetAt (GlobalTheory.RowVacScalar.idemAt w) S (GlobalTheory.VacStab.locPart S v g)
      (GlobalTheory.RowVacScalar.detIdl (GlobalTheory.RowVacScalar.idemAt w) S g) := by
    unfold IsDetAt
    rw [← detIdl_locPart he.1 hε s1, GlobalTheory.RowVacScalar.detIdl_val he.1]
  have hy : IsDetAt (GlobalTheory.RowVacScalar.idemAt w) T (GlobalTheory.VacStab.locPart T v h)
      (GlobalTheory.RowVacScalar.detIdl (GlobalTheory.RowVacScalar.idemAt w) T h) := by
    unfold IsDetAt
    rw [← detIdl_locPart he.1 hε s1, GlobalTheory.RowVacScalar.detIdl_val he.1]
  have sa : SuppAt (GlobalTheory.RowVacScalar.idemAt w) S (GlobalTheory.VacStab.locPart S v g) := fun i j => by
    have := GlobalTheory.VacStab.suppPl_locPart S hε g i j
    rw [hb]; exact this
  have sb : SuppAt (GlobalTheory.RowVacScalar.idemAt w) T (GlobalTheory.VacStab.locPart T v h) := fun i j => by
    have := GlobalTheory.VacStab.suppPl_locPart T hε h i j
    rw [hb]; exact this
  have hL : ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      actO S T (GlobalTheory.VacStab.locPart S v g) (GlobalTheory.VacStab.locPart T v h) u ∈
        latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) ∧
      actO S T (GlobalTheory.VacStab.locPart S v g)⁻¹ (GlobalTheory.VacStab.locPart T v h)⁻¹ u ∈
        latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) := fun u hu =>
    ⟨GlobalTheory.LocalLatStab.actO_mem S T _ _ _ _ _ (fun y hy => (ka y).1 hy) (fun y hy => (kb y).1 hy) u hu,
      GlobalTheory.LocalLatStab.actO_mem S T _ _ _ _ _ (fun y hy => (keeps_inv ka y).1 hy) (fun y hy => (keeps_inv kb y).1 hy) u hu⟩
  have v1 : ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      IsHalf (GlobalTheory.RowVacScalar.idemAt w) u → heisO ψ S T u f = f := fun u hu hh => hvac.2 _ he u hu hh
  have v2 : ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
      IsHalf (cA D (GlobalTheory.RowVacScalar.idemAt w)) u → heisO ψ S T u f = f := fun u hu hh =>
    hvac.2 _ (GlobalTheory.SplitScalar.isSplitIdem_conj he) u hu hh
  exact GlobalTheory.VacStabFixed.om_split_halves hW hΛS hΛT he sa sb hL hx hy hf v1 v2

open Classical in

theorem weilLatticeVacuum_placeSet_induction {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om)
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hΛS : IsSelfDualC S ΛS) (hΛT : IsSelfDualC T ΛT) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (hvac : IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
      fun _ => True) f) :
    ∀ P : Finset (Pl D.host.E), (∀ w ∈ P, Formalism.L2.NTheta.IsIdemAt (GlobalTheory.RowVacScalar.idemAt w) w) →
    Set.InjOn (fun w : Pl D.host.E => w.under (𝓞 D.host.F)) (P : Set (Pl D.host.E)) →
    ∀ g ∈ GfC S, (∀ y, y ∈ latHat D.host.F D.host.E (ΛS : Set (Fin S.rank → D.host.E)) ↔
      ((Formalism.L2.Theta.mt S g).map (finPart D)).mulVec y ∈ latHat D.host.F D.host.E (ΛS : Set (Fin S.rank → D.host.E))) →
    ∀ h ∈ GfC T, (∀ y, y ∈ latHat D.host.F D.host.E (ΛT : Set (Fin T.rank → D.host.E)) ↔
      ((Formalism.L2.Theta.mt T h).map (finPart D)).mulVec y ∈ latHat D.host.F D.host.E (ΛT : Set (Fin T.rank → D.host.E))) →
    (∀ v, (∀ w ∈ P, w.under (𝓞 D.host.F) ≠ v) → (CharUnramAt D χS v ∧ CharUnramAt D χT v) ∨
      (GlobalTheory.VacStab.locPart S v g = 1 ∧ GlobalTheory.VacStab.locPart T v h = 1)) →
    om (g, h) f = (∏ w ∈ P, ((splitFacO χS χT (GlobalTheory.RowVacScalar.detIdl (GlobalTheory.RowVacScalar.idemAt w) S g)
      (GlobalTheory.RowVacScalar.detIdl (GlobalTheory.RowVacScalar.idemAt w) T h) : Circle) : ℂ)) • f := by
  intro P
  induction P using Finset.induction_on with
  | empty =>
    intro _ _ g hg hgk h hh hhk H
    rw [Finset.prod_empty, one_smul]
    exact om_fixed hW hΛS hΛT hf hvac hg hgk hh hhk fun v => H v fun w hw => absurd hw (Finset.notMem_empty w)
  | insert w P hw ih =>
    intro hP hinj g hg hgk h hh hhk H

    have place : ∀ w' ∈ insert w P, ∃ v ε, IsPlaceIdem D v ε ∧
        GlobalTheory.RowVacScalar.idemAt w' + cA D (GlobalTheory.RowVacScalar.idemAt w') = algebraMap (AF D.host.F) (AE D) ε ∧
        w'.under (𝓞 D.host.F) = v := fun w' hw' =>
      GlobalTheory.VacLat.place_of_primeIdem (Or.inl ⟨hP w' hw', rfl⟩)
    have supp : ∀ w' ∈ insert w P, ∀ {v ε}, IsPlaceIdem D v ε →
        GlobalTheory.RowVacScalar.idemAt w' + cA D (GlobalTheory.RowVacScalar.idemAt w') = algebraMap (AF D.host.F) (AE D) ε →
        algebraMap (AF D.host.F) (AE D) ε * GlobalTheory.RowVacScalar.idemAt w' = GlobalTheory.RowVacScalar.idemAt w' :=
      fun w' hw' v ε _ hb => by
        have he := (hP w' hw').1
        rw [← hb]; linear_combination he.1 + he.2.1
    obtain ⟨v, ε, hε, hb, hvw⟩ := place w (Finset.mem_insert_self w P)
    have ka := (inStabAt_locPart (L := ΛS) hgk v).2.2
    have kb := (inStabAt_locPart (L := ΛT) hhk v).2.2

    have hg' : (GlobalTheory.VacStab.locPart S v g)⁻¹ * g ∈ GfC S := mul_mem (inv_mem (locPart_mem v g)) hg
    have hh' : (GlobalTheory.VacStab.locPart T v h)⁻¹ * h ∈ GfC T := mul_mem (inv_mem (locPart_mem v h)) hh
    have hgk' := keeps_mul (keeps_inv ka) hgk
    have hhk' := keeps_mul (keeps_inv kb) hhk
    have hPs : ∀ w' ∈ P, w' ∈ insert w P := fun w' hw' => Finset.mem_insert_of_mem hw'
    have hinj' : Set.InjOn (fun w : Pl D.host.E => w.under (𝓞 D.host.F)) (P : Set (Pl D.host.E)) :=
      hinj.mono (by intro x hx; exact Finset.mem_coe.2 (hPs x (Finset.mem_coe.1 hx)))

    have hne : ∀ w' ∈ P, w'.under (𝓞 D.host.F) ≠ v := fun w' hw' e' => by
      have := hinj (Finset.mem_coe.2 (hPs w' hw')) (Finset.mem_coe.2 (Finset.mem_insert_self w P)) (e'.trans hvw.symm)
      exact hw (this ▸ hw')
    have rest : ∀ {V : HSp D} (k : GA D V) (u : HeightOneSpectrum (𝓞 D.host.F)), u ≠ v →
        GlobalTheory.VacStab.locPart V u ((GlobalTheory.VacStab.locPart V v k)⁻¹ * k) = GlobalTheory.VacStab.locPart V u k := by
      intro V k u hu
      rw [map_mul, map_inv, locPart_locPart_ne hu, inv_one, one_mul]
    have restv : ∀ {V : HSp D} (k : GA D V),
        GlobalTheory.VacStab.locPart V v ((GlobalTheory.VacStab.locPart V v k)⁻¹ * k) = 1 := by
      intro V k
      rw [map_mul, map_inv, locPart_locPart_self, inv_mul_cancel]
    have IH := ih (fun w' hw' => hP w' (hPs w' hw')) hinj' _ hg' hgk' _ hh' hhk' fun u hu => by
      by_cases huv : u = v
      · subst huv
        exact Or.inr ⟨restv g, restv h⟩
      · have hu' : ∀ w' ∈ insert w P, w'.under (𝓞 D.host.F) ≠ u := fun w' hw' => by
          rcases Finset.mem_insert.1 hw' with rfl | hw'
          · exact fun e' => huv (e'.symm.trans hvw)
          · exact hu w' hw'
        rcases H u hu' with hc | ⟨e1, e2⟩
        · exact Or.inl hc
        · exact Or.inr ⟨by rw [rest g u huv, e1], by rw [rest h u huv, e2]⟩

    have fac : ∀ w' ∈ P, ∀ {V : HSp D} (k : GA D V),
        GlobalTheory.RowVacScalar.detIdl (GlobalTheory.RowVacScalar.idemAt w') V ((GlobalTheory.VacStab.locPart V v k)⁻¹ * k) =
          GlobalTheory.RowVacScalar.detIdl (GlobalTheory.RowVacScalar.idemAt w') V k := by
      intro w' hw' V k
      obtain ⟨v', ε', hε', hb', hvw'⟩ := place w' (hPs w' hw')
      have s' := supp w' (hPs w' hw') hε' hb'
      have he' := (hP w' (hPs w' hw')).1.1
      have hvv : v' ≠ v := hvw' ▸ hne w' hw'
      rw [← detIdl_locPart he' hε' s', rest k v' hvv, detIdl_locPart he' hε' s']
    rw [Finset.prod_congr rfl fun w' hw' => by rw [fac w' hw' g, fac w' hw' h]] at IH
    rw [pair_split om g (GlobalTheory.VacStab.locPart S v g) h (GlobalTheory.VacStab.locPart T v h), Module.End.mul_apply, IH, map_smul,
      om_locPart_pair hW hΛS hΛT hf hvac (hP w (Finset.mem_insert_self w P)) hε hb hgk hhk, smul_smul,
      Finset.prod_insert hw, mul_comm]

theorem om_eq_prod_splitFac : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}, IsWeilDatumO ψ S T χS χT om →
    ∀ {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)},
    IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ (P : Finset (Pl D.host.E)), (∀ w ∈ P, Formalism.L2.NTheta.IsIdemAt (GlobalTheory.RowVacScalar.idemAt w) w) →
    Set.InjOn (fun w : Pl D.host.E => w.under (𝓞 D.host.F)) (P : Set (Pl D.host.E)) →
    (∀ v : HeightOneSpectrum (𝓞 D.host.F), (∀ w ∈ P, w.under (𝓞 D.host.F) ≠ v) →
      GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χS v ∧ GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χT v) →
    ∀ g ∈ GfC S, ∀ h ∈ GfC T,
    (∀ y, y ∈ latHat D.host.F D.host.E (ΛS : Set (Fin S.rank → D.host.E)) ↔
      ((Formalism.L2.Theta.mt S g).map (finPart D)).mulVec y ∈ latHat D.host.F D.host.E (ΛS : Set (Fin S.rank → D.host.E))) →
    (∀ y, y ∈ latHat D.host.F D.host.E (ΛT : Set (Fin T.rank → D.host.E)) ↔
      ((Formalism.L2.Theta.mt T h).map (finPart D)).mulVec y ∈ latHat D.host.F D.host.E (ΛT : Set (Fin T.rank → D.host.E))) →
    ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f →
    IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f →
    om (g, h) f = (∏ w ∈ P, ((splitFacO χS χT (GlobalTheory.RowVacScalar.detIdl (GlobalTheory.RowVacScalar.idemAt w) S g)
      (GlobalTheory.RowVacScalar.detIdl (GlobalTheory.RowVacScalar.idemAt w) T h) : Circle) : ℂ)) • f := by
  intro D ψ S T χS χT om hW ΛS ΛT hΛS hΛT P hP hinj hunr g hg h hh hgk hhk f hf hvac
  exact weilLatticeVacuum_placeSet_induction hW hΛS hΛT hf hvac P hP hinj g hg hgk h hh hhk fun v hv => Or.inl (hunr v hv)

end GlobalTheory.LatStabScalar
