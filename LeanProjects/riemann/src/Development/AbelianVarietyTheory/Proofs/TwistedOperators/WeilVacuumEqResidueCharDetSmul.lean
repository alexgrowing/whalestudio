import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameOnOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemCompletedHomLatticeIffFrameStabiliserActionStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEqMulOfResSNeOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.OmVacuumEqSplitFacSmulSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexNeZeroOfFinite

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR GlobalTheory.WeilParts GlobalTheory.StepLaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacLoc

theorem mul_det_eq {R n : Type} [CommRing R] [Fintype n] [DecidableEq n] (a : R) (M : Matrix n n R)
    (h : ∀ i j, a * (M - 1) i j = 0) : a * M.det = a := by
  let I : Ideal R := LinearMap.ker (LinearMap.mulLeft R a)
  have h1 : (Ideal.Quotient.mk I).mapMatrix M = (Ideal.Quotient.mk I).mapMatrix 1 :=
    Matrix.ext fun i j => Ideal.Quotient.eq.2 (h i j)
  have h2 : Ideal.Quotient.mk I M.det = Ideal.Quotient.mk I 1 := by
    rw [RingHom.map_det, h1, map_one, Matrix.det_one, map_one]
  have h3 : a * (M.det - 1) = 0 := Ideal.Quotient.eq.1 h2
  linear_combination h3

theorem unit_aux {R : Type} [CommRing R] {a d d' : R} (ha : a * a = a) (hd : d * d' = 1) :
    (a * d + (1 - a)) * (a * d' + (1 - a)) = 1 := by
  linear_combination a * hd + (d * d' - d - d' + 1) * ha

theorem exists_unit {R : Type} [CommRing R] {a d d' : R} (ha : a * a = a) (hd : d * d' = 1) :
    ∃ x : Rˣ, (x : R) = a * d + (1 - a) ∧ ((x⁻¹ : Rˣ) : R) = a * d' + (1 - a) :=
  ⟨⟨_, _, unit_aux ha hd, (mul_comm _ _).trans (unit_aux ha hd)⟩, rfl, rfl⟩

theorem mul_of_orth {R : Type} [CommRing R] {a b d x : R} (hx : x = a * d + (1 - a)) (h : b * a = 0) : b * x = b := by
  rw [hx]; linear_combination (d - 1) * h

theorem mul_of_idem {R : Type} [CommRing R] {a d x : R} (hx : x = a * d + (1 - a)) (h : a * a = a) : a * x = a * d := by
  rw [hx]; linear_combination (d - 1) * h

theorem mul_zero_of {R : Type} [CommRing R] {b c z : R} (hz : c * z = z) (h : b * c = 0) : b * z = 0 := by
  rw [← hz, ← mul_assoc, h, zero_mul]

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem resS_eq_gen (PP : Pl E) {a x y : E ⊗[F] Formalism.L2.Herm.Af F} (ha : a ∈ Formalism.L2.Herm.intAf F E)
    (hx : x ∈ Formalism.L2.Herm.intAf F E) (hy : y ∈ Formalism.L2.Herm.intAf F E) (h1 : resS F PP ⟨a, ha⟩ = 1)
    (h : a * x = a * y) : resS F PP ⟨x, hx⟩ = resS F PP ⟨y, hy⟩ := by
  have e : (⟨a, ha⟩ : Formalism.L2.Herm.intAf F E) * ⟨x, hx⟩ = ⟨a, ha⟩ * ⟨y, hy⟩ := Subtype.ext h
  have := congrArg (resS F PP) e
  rwa [map_mul, map_mul, h1, one_mul, one_mul] at this

theorem det_int_gen {n : ℕ} {β g : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hg : g ∈ St β)
    {d : E ⊗[F] Formalism.L2.Herm.Af F} (hd : d = g.val.det) :
    ∃ h : d ∈ Formalism.L2.Herm.intAf F E, ∀ PP : Pl E,
      ((Matrix.GeneralLinearGroup.det (redFn β PP g) : (kP PP)ˣ) : kP PP) = resS F PP ⟨d, h⟩ := by
  obtain ⟨y, rfl⟩ := hg
  have h3 : d = (y.val.det : Formalism.L2.Herm.intAf F E) := by
    rw [hd]
    change (β * intGL _ _ _ y * β⁻¹).val.det = _
    rw [Units.val_mul, Units.val_mul, Matrix.det_units_conj]
    exact ((Formalism.L2.Herm.intAf F E).subtype.map_det y.val).symm
  subst h3
  refine ⟨y.val.det.2, fun PP => ?_⟩
  rw [redFn_frGL]
  exact ((resS F PP).map_det y.val).symm

theorem mem_aux {a d : E ⊗[F] Formalism.L2.Herm.Af F} (ha : a ∈ Formalism.L2.Herm.intAf F E) (hd : d ∈ Formalism.L2.Herm.intAf F E) :
    a * d + (1 - a) ∈ Formalism.L2.Herm.intAf F E := add_mem (mul_mem ha hd) (sub_mem (one_mem _) ha)

end General

variable {D : D7}

theorem resS_eq_of_idem {a : AE D} {PP : Pl D.host.E} (ha : Formalism.L2.NTheta.IsIdemAt a PP) {x y : AE D}
    (hx : toEAf D x ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (hy : toEAf D y ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (h : a * x = a * y) : resS D.host.F PP ⟨toEAf D x, hx⟩ = resS D.host.F PP ⟨toEAf D y, hy⟩ := by
  obtain ⟨hi, h1⟩ := GlobalTheory.IdemRes.resS_idem_eq_one D a PP ha
  exact resS_eq_gen PP hi hx hy h1 (by rw [← RingHom.map_mul, h, RingHom.map_mul])

theorem det_int {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {g : GA D V} (hg : finE V g ∈ St β) :
    ∃ h : toEAf D (Formalism.L2.Theta.mt V g).det ∈ Formalism.L2.Herm.intAf D.host.F D.host.E, ∀ PP : Pl D.host.E,
      ((Matrix.GeneralLinearGroup.det (redFn β PP (finE V g)) : (kP PP)ˣ) : kP PP) =
        resS D.host.F PP ⟨_, h⟩ :=
  det_int_gen hg ((toEAf D).map_det _)

theorem det_mul_det_inv (V : HSp D) (g : GA D V) :
    (Formalism.L2.Theta.mt V g).det * (Formalism.L2.Theta.mt V g⁻¹).det = 1 := by
  unfold Formalism.L2.Theta.mt
  rw [← Matrix.det_mul, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.det_one]

set_option maxHeartbeats 800000 in

theorem exists_detAt {χ : (AE D)ˣ →* Circle} {P : Finset (Pl D.host.E)} {es : Pl D.host.E → AE D}
    (hes : ∀ PP ∈ P, Formalism.L2.NTheta.IsIdemAt (es PP) PP) {e : AE D} {c : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ}
    (hχ : TameOn χ e P c) {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {g : GA D V} (hg : finE V g ∈ St β)
    {ε : AF D.host.F} (hs : SuppPl ε V g) {a : AE D} (ha : a * a = a) (hinf : infPart D a = 0) (hc : cA D e * a = 0)
    (hP : ∀ PP ∈ P, es PP = a ∨ (es PP * algebraMap (AF D.host.F) (AE D) ε = 0 ∧ es PP * a = 0)) :
    ∃ x : (AE D)ˣ, IsDetAt a V g x ∧
      ((χ x : Circle) : ℂ) = ∏ PP ∈ P, ((c PP (Matrix.GeneralLinearGroup.det (redFn β PP (finE V g))) : ℂˣ) : ℂ) := by
  obtain ⟨h1, hr⟩ := det_int hg
  obtain ⟨h2, -⟩ := det_int (g := g⁻¹) (β := β) (by rw [map_inv]; exact inv_mem hg)
  have hai : toEAf D a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
    GlobalTheory.IdemRes.toEAf_mem_of_finPart (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha]))
  have hint : ∀ d : AE D, toEAf D d ∈ Formalism.L2.Herm.intAf D.host.F D.host.E →
      toEAf D (a * d + (1 - a)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun d hd => by
    rw [RingHom.map_add, RingHom.map_mul, RingHom.map_sub, RingHom.map_one]
    exact mem_aux hai hd
  obtain ⟨x, hx, hx'⟩ := exists_unit ha (det_mul_det_inv V g)
  have i1 : toEAf D (x : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by rw [hx]; exact hint _ h1
  have i2 : toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by rw [hx']; exact hint _ h2
  refine ⟨x, hx, hχ x ?_ i1 i2 (mul_of_orth hx hc)
    (fun PP => Matrix.GeneralLinearGroup.det (redFn β PP (finE V g))) fun PP hPP => ?_⟩
  · rw [hx, RingHom.map_add, RingHom.map_mul, RingHom.map_sub, RingHom.map_one, hinf, zero_mul, zero_add, sub_zero]
  · have k : es PP * (Formalism.L2.Theta.mt V g).det = es PP * (x : AE D) := by
      rcases hP PP hPP with h | ⟨k1, k2⟩
      · rw [h]; exact (mul_of_idem hx ha).symm
      · exact (mul_det_eq _ _ fun i j => mul_zero_of (hs i j) k1).trans (mul_of_orth hx k2).symm
    have k1 := resS_eq_of_idem (hes PP hPP) h1 i1 k
    rw [← k1]
    exact hr PP

theorem split_cases {a : AE D} (ha : IsSplitIdem D a) {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F}
    (hε : IsPlaceIdem D v ε) : a + cA D a = algebraMap (AF D.host.F) (AE D) ε ∨
      (a * algebraMap (AF D.host.F) (AE D) ε = 0 ∧ cA D a * algebraMap (AF D.host.F) (AE D) ε = 0) := by
  obtain ⟨a1, a2, v', ε', hε', a3⟩ := ha
  by_cases hv : v' = v
  · subst hv
    exact Or.inl (GlobalTheory.PlaceDatum.placeIdem_eq hε' hε ▸ a3)
  · have h0 : (a + cA D a) * algebraMap (AF D.host.F) (AE D) ε = 0 := by
      rw [a3, ← RingHom.map_mul, GlobalTheory.PlaceDatum.placeIdem_mul hε' hε hv, RingHom.map_zero]
    have h1 : a * algebraMap (AF D.host.F) (AE D) ε = 0 := by
      have : a = a * (a + cA D a) := by rw [mul_add, a1, a2, add_zero]
      rw [this, mul_assoc, h0, mul_zero]
    refine Or.inr ⟨h1, ?_⟩
    rwa [add_mul, h1, zero_add] at h0

theorem cA_sum_mul {P : Finset (Pl D.host.E)} {es : Pl D.host.E → AE D} {a : AE D}
    (h : ∀ PP ∈ P, cA D (es PP) * a = 0) : cA D (∑ PP ∈ P, es PP) * a = 0 := by
  rw [map_sum (cA D), Finset.sum_mul]
  exact Finset.sum_eq_zero h

theorem unramAt_of_tame {χ : (AE D)ˣ →* Circle} {P : Finset (Pl D.host.E)} {es : Pl D.host.E → AE D}
    (hes : ∀ PP ∈ P, Formalism.L2.NTheta.IsIdemAt (es PP) PP) {c : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ}
    (hχ : TameOn χ (∑ PP ∈ P, es PP) P c) {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F}
    (hε : IsPlaceIdem D v ε) (h : ∀ PP ∈ P, es PP * algebraMap (AF D.host.F) (AE D) ε = 0 ∧
      cA D (es PP) * algebraMap (AF D.host.F) (AE D) ε = 0) : UnramAt ε χ := by
  intro x hx h1 h2
  have h0 : infPart D (algebraMap (AF D.host.F) (AE D) ε) = 0 := by
    obtain ⟨α, rfl, -⟩ := hε
    exact TensorProduct.zero_tmul _ _
  have k : ∀ b : AE D, b * algebraMap (AF D.host.F) (AE D) ε = 0 → b * (x : AE D) = b := fun b hb => by
    have : b * ((x : AE D) - 1) = 0 := by rw [← hx, ← mul_assoc, hb, zero_mul]
    rwa [mul_sub, mul_one, sub_eq_zero] at this
  have h3 : toEAf D 1 ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by rw [RingHom.map_one]; exact one_mem _
  have := hχ x ?_ (GlobalTheory.IdemRes.toEAf_mem_of_finPart h1) (GlobalTheory.IdemRes.toEAf_mem_of_finPart h2)
    (k _ (cA_sum_mul fun PP hPP => (h PP hPP).2)) (fun _ => 1) fun PP hPP => ?_
  · apply Circle.ext
    rw [this]
    simp
  · have := congrArg (infPart D) hx
    rwa [RingHom.map_mul, h0, zero_mul, RingHom.map_sub, RingHom.map_one, eq_comm, sub_eq_zero] at this
  · rw [resS_eq_of_idem (hes PP hPP) _ h3 (by rw [k _ (h PP hPP).1, mul_one]),
      show (⟨_, h3⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = 1 from Subtype.ext (toEAf D).map_one, map_one]
    rfl

theorem place_smul_latO {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) {u : WO S T}
    (hu : u ∈ latO S T LS LT fun w => w = v) : algebraMap (AF D.host.F) (AE D) ε • u = u := by
  obtain ⟨β, rfl, h1, h0⟩ := hε
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, -, hα, a, -, s, -, t, -, rfl⟩ := hw
    have h : pairA D.host.F 0 β * pairA D.host.F 0 α = pairA D.host.F 0 α := by
      refine Prod.ext (mul_zero _) ?_
      change β * α = α
      refine RestrictedProduct.ext _ _ fun w => ?_
      change evalV D.host.F w (β * α) = evalV D.host.F w α
      rw [map_mul]
      by_cases hw : w = v
      · subst hw; rw [h1, one_mul]
      · rw [hα w hw, mul_zero]
    refine Matrix.ext fun i j => ?_
    change (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E)) * (pairA D.host.F 0 α ⊗ₜ[D.host.F] _) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, h, one_mul]
    rfl
  | zero => exact smul_zero _
  | add x y _ _ hx hy => rw [smul_add, hx, hy]
  | neg x _ hx => rw [smul_neg, hx]

theorem latO_le {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    (Pv : HeightOneSpectrum (𝓞 D.host.F) → Prop) : latO S T LS LT Pv ≤ latO S T LS LT fun _ => True := by
  refine AddSubgroup.closure_mono ?_
  rintro _ ⟨α, hα, -, h⟩
  exact ⟨α, hα, fun v hv => absurd trivial hv, h⟩

theorem vacScal_eq {S T : HSp D} {βS : GL (Fin S.rank) (Lev.EAf D)} {βT : GL (Fin T.rank) (Lev.EAf D)}
    {P : Finset (Pl D.host.E)} {cS cT : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ} {g : GA D S} {h : GA D T}
    {χS χT : (AE D)ˣ →* Circle} {x y : (AE D)ˣ}
    (hx : ((χT x : Circle) : ℂ) =
      ∏ PP ∈ P, ((cT PP (Matrix.GeneralLinearGroup.det (redFn βS PP (finE S g))) : ℂˣ) : ℂ))
    (hy : ((χS y : Circle) : ℂ) =
      ∏ PP ∈ P, ((cS PP (Matrix.GeneralLinearGroup.det (redFn βT PP (finE T h))) : ℂˣ) : ℂ)) :
    vacScal βS βT P cS cT g h = (splitFacO χS χT x y : ℂ) := by
  rw [vacScal, Finset.prod_mul_distrib, Finset.prod_inv_distrib, ← hx, ← hy, splitFacO, Circle.coe_mul, Circle.coe_inv]

theorem eq_one_of_detAt_zero {V : HSp D} {g : GA D V} {x : (AE D)ˣ} (h : IsDetAt 0 V g x) : x = 1 :=
  Units.ext ((show (x : AE D) = _ from h).trans (by rw [zero_mul, zero_add, sub_zero, Units.val_one]))

theorem exists_adapted {P : Finset (Pl D.host.E)} {es : Pl D.host.E → AE D}
    (hes : ∀ PP ∈ P, Formalism.L2.NTheta.IsIdemAt (es PP) PP)
    (hc : (∑ PP ∈ P, es PP) * cA D (∑ PP ∈ P, es PP) = 0) {v : HeightOneSpectrum (𝓞 D.host.F)} {ε : AF D.host.F}
    (hε : IsPlaceIdem D v ε) {b : AE D} (hb : IsSplitIdem D b)
    (hbε : b + cA D b = algebraMap (AF D.host.F) (AE D) ε) :
    ∃ a : AE D, IsSplitIdem D a ∧ a + cA D a = algebraMap (AF D.host.F) (AE D) ε ∧ cA D (∑ PP ∈ P, es PP) * a = 0 ∧
      ∀ PP ∈ P, es PP = a ∨ (es PP * algebraMap (AF D.host.F) (AE D) ε = 0 ∧ es PP * a = 0) := by
  have hcross : ∀ i ∈ P, ∀ j ∈ P, es i * cA D (es j) = 0 :=
    GlobalTheory.PlaceDatum.cross_eq_zero (R := AE D) GlobalTheory.PlaceDatum.isUnit_natCast (cA D) es P (fun i hi => (hes i hi).1.1) hc
  have hz : ∀ a : AE D, IsSplitIdem D a → a + cA D a = algebraMap (AF D.host.F) (AE D) ε →
      algebraMap (AF D.host.F) (AE D) ε * a = a := fun a ha h => by
    rw [← h, add_mul, ha.1, mul_comm, ha.2.1, add_zero]
  by_cases h : ∃ Q ∈ P, es Q + cA D (es Q) = algebraMap (AF D.host.F) (AE D) ε
  · obtain ⟨Q, hQ, h⟩ := h
    have hq := (hes Q hQ).1
    refine ⟨es Q, hq, h, cA_sum_mul fun PP hPP => (mul_comm _ _).trans (hcross Q hQ PP hPP), fun PP hPP => ?_⟩
    have hp := (hes PP hPP).1
    rcases split_cases hp hε with k | k
    · exact Or.inl (GlobalTheory.PlaceDatum.idempotent_eq_of_orthogonal_decomp hp.1 hp.2.1 hq.1 hq.2.1 (k.trans h.symm) (hcross PP hPP Q hQ)
        (hcross Q hQ PP hPP))
    · exact Or.inr ⟨k.1, mul_zero_of (hz _ hq h) k.1⟩
  · have k := fun PP hPP => (split_cases (hes PP hPP).1 hε).resolve_left fun k => h ⟨PP, hPP, k⟩
    exact ⟨b, hb, hbε, cA_sum_mul fun PP hPP => mul_zero_of (hz _ hb hbε) (k PP hPP).2,
      fun PP hPP => Or.inr ⟨(k PP hPP).1, mul_zero_of (hz _ hb hbε) (k PP hPP).1⟩⟩

theorem om_vacuum_eq_vacScal_smul : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (θ : InfFam D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D)) (e : AE D) (P : Finset (Pl D.host.E)) (cS cT : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (f : WO S T → ℂ), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → S.SigOK → T.SigOK → (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → IsFrame βS ΛS → IsFrame βT ΛT → IsIdemSum e P → TameOn χS e P cS → TameOn χT e P cT → (∀ v ε, NonSplitAt D v ε → UnramAt ε χS → UnramAt ε χT → FixesVacAt ψ S T ΛS ΛT om v ε) → IsVacO ψ θ S T sS sT ΛS ΛT f → ∀ g ∈ GfC S, ∀ h ∈ GfC T, finE S g ∈ St βS → finE T h ∈ St βT → ∀ v ε, IsPlaceIdem D v ε → SuppPl ε S g → SuppPl ε T h → om (g, h) f = vacScal βS βT P cS cT g h • f := by
  intro D ψ S T χS χT om θ sS sT ΛS ΛT βS βT e P cS cT f hW hθ hS hT hsS hsT hΛS hΛT hβS hβT he hχS hχT hfix hf
    g _ h _ hg hh v ε hε hgε hhε
  obtain ⟨⟨es, hes, rfl⟩, hc⟩ := he
  have hstab := GlobalTheory.T.mem_completedHomLattice_iff_frameStabiliser_action D S T ΛS ΛT βS βT hΛS.1 hΛT.1 hβS hβT g h hg hh
  by_cases hsp : ∃ b : AE D, IsSplitIdem D b ∧ b + cA D b = algebraMap (AF D.host.F) (AE D) ε
  · obtain ⟨b, hb, hbε⟩ := hsp
    obtain ⟨a, ha, haε, hca, hP⟩ := exists_adapted hes hc hε hb hbε
    obtain ⟨x, hx, hx'⟩ := exists_detAt hes hχT hg hgε ha.1 (GlobalTheory.SplitScalar.infPart_splitIdem ha) hca hP
    obtain ⟨y, hy, hy'⟩ := exists_detAt hes hχS hh hhε ha.1 (GlobalTheory.SplitScalar.infPart_splitIdem ha) hca hP
    have hR : ∀ (c : AE D), ∀ u ∈ ({0} : Finset (WO S T)), u ∈ (latO S T ΛS ΛT fun _ => True) ∧ IsHalf c u :=
      fun c u hu => by
        rw [Finset.mem_singleton.1 hu]
        exact ⟨zero_mem _, GlobalTheory.SplitScalar.isHalf_zero c⟩
    have hRu : ∀ (c : AE D), ∀ u ∈ (latO S T ΛS ΛT fun _ => True), IsHalf c u →
        ∃! w, w ∈ ({0} : Finset (WO S T)) ∧ u - w ∈ (latO S T ΛS ΛT fun _ => True) :=
      fun c u hu _ => ⟨0, ⟨Finset.mem_singleton_self _, sub_mem hu (zero_mem _)⟩,
        fun w hw => Finset.mem_singleton.1 hw.1⟩
    have key := GlobalTheory.SplitScalar.om_vacuum_eq_splitFac_smul_sum D ψ θ S T χS χT om hW hθ hS hT sS sT hsS hsT
      ΛS ΛS ΛT ΛT hΛS hΛS hΛT hΛT a ha g h (fun i j => by rw [haε]; exact hgε i j)
      (fun i j => by rw [haε]; exact hhε i j) x y hx hy
      (fun u => ⟨fun hu => ⟨actO S T g⁻¹ h⁻¹ u, (hstab _ _).2 (by rwa [GlobalTheory.AdelicLatMove.actO_actO_inv]), (GlobalTheory.AdelicLatMove.actO_actO_inv S T g h u).symm⟩,
        fun ⟨u₀, hu₀, e⟩ => e ▸ (hstab _ _).1 hu₀⟩) {0} {0} (hR _) (hRu _) (hR _) (hRu _) f hf
    rw [key, vacScal_eq hx' hy', Finset.sum_singleton, Finset.sum_singleton, GlobalTheory.SplitScalar.heisO_zero,
      GlobalTheory.SplitScalar.heisO_zero, Finset.card_singleton]
    simp
  · have hn : NonSplitAt D v ε := ⟨hε, hsp⟩
    have k := fun PP hPP => (split_cases (hes PP hPP).1 hε).resolve_left fun k => hsp ⟨_, (hes PP hPP).1, k⟩
    have hP : ∀ PP ∈ P, es PP = 0 ∨ (es PP * algebraMap (AF D.host.F) (AE D) ε = 0 ∧ es PP * 0 = 0) :=
      fun PP hPP => Or.inr ⟨(k PP hPP).1, mul_zero _⟩
    obtain ⟨x, hx, hx'⟩ := exists_detAt hes hχT hg hgε (mul_zero 0) (infPart D).map_zero (mul_zero _) hP
    obtain ⟨y, hy, hy'⟩ := exists_detAt hes hχS hh hhε (mul_zero 0) (infPart D).map_zero (mul_zero _) hP
    rw [vacScal_eq hx' hy', eq_one_of_detAt_zero hx, eq_one_of_detAt_zero hy, splitFacO, map_one, map_one, inv_one,
      one_mul, Circle.coe_one, one_smul]
    refine hfix v ε hn (unramAt_of_tame hes hχS hε k) (unramAt_of_tame hes hχT hε k) g h hgε hhε (hstab _) f hf.2.theta
      fun u hu => ?_
    obtain ⟨a, ha, h2⟩ := GlobalTheory.FinWeilO.exists_half_of_nonSplit hn
    have h3 := hf.2.lat.1 _ (latO_le _ (GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a ha u hu))
    have h4 : 2 • (a • u) = u := by
      rw [two_nsmul, ← add_smul, ← two_mul, h2, place_smul_latO hε hu]
    rwa [h4] at h3

end GlobalTheory.VacLoc

end
