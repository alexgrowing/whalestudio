import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UniformLevelMultiplicity
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelLiftConditions
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelSubgroup
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicElementLatticeFullAndCompletion
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongruenceLatticeFractionalMultipleAgree
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitDeterminantCongruentElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalVectorMemIdealCompletedLatticeIffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelGroupLatticeCongruence
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeAutomorphismModHalfLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteUnitChineseRemainder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnifEvery

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level)
open GlobalTheory.IndefiniteRowSideFullHecke.EmbeddingLevelSets (IsCover)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelLiftConditions (LevGrp levDet idealHat CongMod IsInvTame IsLevLift)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev iA (D : D7) (b : 𝓞 D.host.E) : Af D.host.F ⊗[D.host.F] D.host.E := (1 : Af D.host.F) ⊗ₜ (b : D.host.E)

theorem iA_mul (a b : 𝓞 D.host.E) : iA D (a * b) = iA D a * iA D b := by
  simp [iA, Algebra.TensorProduct.tmul_mul_tmul]

theorem iA_add (a b : 𝓞 D.host.E) : iA D (a + b) = iA D a + iA D b := by
  simp [iA, TensorProduct.tmul_add]

theorem iA_one : iA D 1 = 1 := by simp [iA, Algebra.TensorProduct.one_def]

theorem iA_nat (n : ℕ) : iA D n = n := by
  induction n with
  | zero => simp [iA]
  | succ n ih => rw [Nat.cast_succ, iA_add, ih, iA_one, Nat.cast_succ]

variable (V : HSp D)

def idl (I : Ideal (𝓞 D.host.E)) : AddSubgroup (Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :=
  AddSubgroup.closure {u | ∃ b ∈ I, ∃ z ∈ latGHat V 1, u = halfVec V b z}

variable {V}

theorem halfVec_eq (b : 𝓞 D.host.E) (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    halfVec V b z = iA D b • z := rfl

theorem finVec_add (a b : Fin V.rank → D.host.E) : finVec V (a + b) = finVec V a + finVec V b :=
  GlobalTheory.Member.AALev.fv_add a b

theorem finVec_sub (a b : Fin V.rank → D.host.E) : finVec V (a - b) = finVec V a - finVec V b := by
  rw [eq_sub_iff_add_eq, ← finVec_add, sub_add_cancel]

theorem finVec_smul (b : 𝓞 D.host.E) (a : Fin V.rank → D.host.E) : finVec V (b • a) = iA D b • finVec V a :=
  GlobalTheory.Member.AALev.fv_smul (b : D.host.E) a

theorem smul_mem_hat {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) {y : Af D.host.F ⊗[D.host.F] D.host.E}
    (hy : y ∈ intAE D) {z : Fin n → Af D.host.F ⊗[D.host.F] D.host.E}
    (hz : z ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E))) :
    y • z ∈ GlobalTheory.AdLat.hat D.host.F (L : Set (Fin n → D.host.E)) := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, rfl⟩ := hy
    have h := GlobalTheory.Member.AALev.hat_smul_adele _ a ha (GlobalTheory.Member.AALev.hat_smul_int L x hz)
    rwa [smul_smul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at h
  | zero => rw [zero_smul]; exact zero_mem _
  | add x y _ _ hx hy => rw [add_smul]; exact add_mem hx hy
  | neg x _ hx => rw [neg_smul]; exact neg_mem hx

theorem latGHat_one (V : HSp D) : latGHat V 1 = GlobalTheory.AdLat.hat D.host.F (latG V 1 : Set (Fin V.rank → D.host.E)) :=
  (GlobalTheory.Member.latG_lattice_and_completion D V 1).2.2.2.2.1

theorem smul_mem_latGHat {y : Af D.host.F ⊗[D.host.F] D.host.E} (hy : y ∈ intAE D)
    {z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E} (hz : z ∈ latGHat V 1) : y • z ∈ latGHat V 1 := by
  rw [latGHat_one] at hz ⊢
  exact smul_mem_hat _ hy hz

theorem smul_mem_latHat {y : Af D.host.F ⊗[D.host.F] D.host.E} (hy : y ∈ intAE D)
    {z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E} (hz : z ∈ latHat V) : y • z ∈ latHat V := by
  rw [GlobalTheory.Member.AALev.latHat_eq] at hz ⊢
  exact smul_mem_hat _ hy hz

theorem iA_mem (b : 𝓞 D.host.E) : iA D b ∈ intAE D :=
  AddSubgroup.subset_closure ⟨1, fun _ => one_mem _, b, rfl⟩

theorem finVec_mem {a : Fin V.rank → D.host.E} (ha : a ∈ latG V 1) : finVec V a ∈ latGHat V 1 := by
  rw [latGHat_one]
  exact GlobalTheory.Member.AALev.fv_mem_hat _ ha

theorem smul_mem_idl {I : Ideal (𝓞 D.host.E)} {b : 𝓞 D.host.E} (hb : b ∈ I)
    {z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E} (hz : z ∈ latGHat V 1) : iA D b • z ∈ idl V I :=
  AddSubgroup.subset_closure ⟨b, hb, z, hz, rfl⟩

theorem mem_levSet_one {κ : GA D V} :
    κ ∈ IndefiniteRowSideFullHecke.EmbeddingLevelSets.levSet V 1 ↔ κ ∈ GfC V ∧ ∀ z ∈ latHat V, (finHom V κ).1 *ᵥ z ∈ latHat V := by
  refine and_congr Iff.rfl (forall₂_congr fun z hz => ⟨?_, fun h => ⟨_, sub_mem h hz, (one_smul _ _).symm⟩⟩)
  rintro ⟨y, hy, e⟩
  rw [one_smul, sub_eq_iff_eq_add] at e
  exact e ▸ add_mem hy hz

theorem finHom_mul (κ κ' : GA D V) (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    (finHom V (κ * κ')).1 *ᵥ z = (finHom V κ).1 *ᵥ ((finHom V κ').1 *ᵥ z) := by
  rw [map_mul, Units.val_mul, Matrix.mulVec_mulVec]

theorem levSet_mul {κ κ' : GA D V} (h : κ ∈ IndefiniteRowSideFullHecke.EmbeddingLevelSets.levSet V 1) (h' : κ' ∈ IndefiniteRowSideFullHecke.EmbeddingLevelSets.levSet V 1) : κ * κ' ∈ IndefiniteRowSideFullHecke.EmbeddingLevelSets.levSet V 1 := by
  rw [mem_levSet_one] at h h' ⊢
  exact ⟨mul_mem h.1 h'.1, fun z hz => finHom_mul κ κ' z ▸ h.2 _ (h'.2 z hz)⟩

theorem stab_latGHat {κ : GA D V} (h : κ ∈ IndefiniteRowSideFullHecke.EmbeddingLevelSets.levSet V 1) {z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E}
    (hz : z ∈ latGHat V 1) : (finHom V κ).1 *ᵥ z ∈ latGHat V 1 :=
  (GlobalTheory.Member.AALev.congruences_agree D V κ).1.2 h.2 z hz

theorem stab_idl {κ : GA D V} (h : κ ∈ IndefiniteRowSideFullHecke.EmbeddingLevelSets.levSet V 1) {I : Ideal (𝓞 D.host.E)}
    {z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E} (hz : z ∈ idl V I) : (finHom V κ).1 *ᵥ z ∈ idl V I := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, z, hz, rfl⟩ := hy
    rw [halfVec_eq, Matrix.mulVec_smul]
    exact smul_mem_idl hb (stab_latGHat h hz)
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.mulVec_neg]; exact neg_mem hx

theorem smul_neg_eq {A : Type} [CommRing A] {n : ℕ} (b : A) (x w : Fin n → A) (M : ℕ) (e : b • x = M • w) :
    b • -x = M • -w := by rw [smul_neg, smul_neg, e]

theorem smul_idl_eq {I J : Ideal (𝓞 D.host.E)} {M : ℕ} (h : I * J = Ideal.span {(M : 𝓞 D.host.E)}) {b : 𝓞 D.host.E}
    (hb : b ∈ I) {u : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E} (hu : u ∈ idl V J) :
    ∃ w ∈ latGHat V 1, iA D b • u = M • w := by
  induction hu using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b', hb', z, hz, rfl⟩ := hy
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 (h ▸ Ideal.mul_mem_mul hb hb')
    refine ⟨iA D r • z, smul_mem_latGHat (iA_mem r) hz, ?_⟩
    rw [halfVec_eq, smul_smul, ← iA_mul, ← hr, mul_comm, iA_mul, iA_nat, mul_smul, Nat.cast_smul_eq_nsmul]
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨w, hw, e⟩ := hx
    obtain ⟨w', hw', e'⟩ := hy
    exact ⟨w + w', add_mem hw hw', by rw [smul_add, smul_add, e, e']⟩
  | neg x _ hx =>
    obtain ⟨w, hw, e⟩ := hx
    exact ⟨-w, neg_mem hw, smul_neg_eq _ _ _ _ e⟩

theorem inf_idl {I J : Ideal (𝓞 D.host.E)} {M : ℕ} (h : I * J = Ideal.span {(M : 𝓞 D.host.E)}) (hc : I ⊔ J = ⊤)
    {u : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E} (hI : u ∈ idl V I) (hJ : u ∈ idl V J) :
    ∃ w ∈ latGHat V 1, u = M • w := by
  obtain ⟨m, hm, c, hc', e⟩ := Submodule.mem_sup.1 (hc ▸ Submodule.mem_top : (1 : 𝓞 D.host.E) ∈ I ⊔ J)
  obtain ⟨w, hw, e1⟩ := smul_idl_eq h hm hJ
  obtain ⟨w', hw', e2⟩ := smul_idl_eq (mul_comm I J ▸ h) hc' hI
  refine ⟨w + w', add_mem hw hw', ?_⟩
  rw [smul_add, ← e1, ← e2, ← add_smul, ← iA_add, e, iA_one, one_smul]

section Lev

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} (l : Level H)

abbrev Mc : Ideal (𝓞 D.host.E) := l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)

theorem span_ne : Ideal.span {(l.M : 𝓞 D.host.E)} ≠ ⊥ := by
  rw [Ne, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
  have := l.three_le
  omega

theorem Mb_ne : l.Mb ≠ ⊥ := fun h => span_ne l (by rw [← l.prod, h, Ideal.bot_mul])

theorem Mc_ne : Mc l ≠ ⊥ := fun h => span_ne l (by rw [← l.prod, show l.Mb.map _ = ⊥ from h, Ideal.mul_bot])

theorem M_mem : (l.M : 𝓞 D.host.E) ∈ l.Mb := by
  have h := Ideal.mem_span_singleton_self (l.M : 𝓞 D.host.E)
  rw [← l.prod] at h
  exact (Ideal.mul_le_inf h).1

theorem exists_split : ∃ m ∈ l.Mb, ∃ c ∈ Mc l, m + c = 1 :=
  Submodule.mem_sup.1 (by rw [show l.Mb ⊔ Mc l = ⊤ from l.coprime]; exact Submodule.mem_top)

variable (V) in

def Ind (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (γ : LevGrp Dw l) (κ : GA D V) : Prop :=
  κ ∈ IndefiniteRowSideFullHecke.EmbeddingLevelSets.levSet V 1 ∧ ∀ a : Dw.La, (finHom V κ).1 *ᵥ finVec V (ι a) - finVec V (ι (liftLa γ a)) ∈ idl V l.Mb

variable {l} {ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)}

theorem iota_mem (hι : LatEmb V ι) (a : Dw.La) : finVec V (ι a) ∈ latGHat V 1 :=
  finVec_mem (hι.2 ▸ LinearMap.mem_range_self ι a)

theorem map_smul_top (hι : LatEmb V ι) (I : Ideal (𝓞 D.host.E)) :
    (I • (⊤ : Submodule (𝓞 D.host.E) Dw.La)).map ι = I • latG V 1 := by
  rw [Submodule.map_smul'', Submodule.map_top, hι.2]

theorem iota_mem_idl (hι : LatEmb V ι) {I : Ideal (𝓞 D.host.E)} (hI : I ≠ ⊥) (a : Dw.La) :
    finVec V (ι a) ∈ idl V I ↔ a ∈ I • (⊤ : Submodule (𝓞 D.host.E) Dw.La) := by
  refine (GlobalTheory.T.rationalVector_mem_ideal_completedLattice_iff D V I hI (ι a)).trans ?_
  rw [← map_smul_top hι]
  exact ⟨fun ⟨b, hb, e⟩ => hι.1 e ▸ hb, fun h => ⟨a, h, rfl⟩⟩

theorem sub_mem_idl (hι : LatEmb V ι) (a a' : Dw.La) :
    finVec V (ι a) - finVec V (ι a') ∈ idl V l.Mb ↔
      (l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)).mkQ a = (l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)).mkQ a' := by
  rw [← finVec_sub, ← map_sub, iota_mem_idl hι (Mb_ne l), Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]

theorem Ind.unique (hι : LatEmb V ι) {γ γ' : LevGrp Dw l} {κ : GA D V} (h : Ind V l ι γ κ) (h' : Ind V l ι γ' κ) :
    γ = γ' := by
  refine LinearEquiv.ext fun q => ?_
  obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective _ q
  rw [← liftLa_spec, ← liftLa_spec, ← sub_mem_idl hι]
  have := sub_mem (h'.2 a) (h.2 a)
  rwa [sub_sub_sub_cancel_left] at this

theorem Ind.mul (hι : LatEmb V ι) {γ γ' : LevGrp Dw l} {κ κ' : GA D V} (h : Ind V l ι γ κ) (h' : Ind V l ι γ' κ') :
    Ind V l ι (γ * γ') (κ * κ') := by
  refine ⟨levSet_mul h.1 h'.1, fun a => ?_⟩
  have h3 : finVec V (ι (liftLa γ (liftLa γ' a))) - finVec V (ι (liftLa (γ * γ') a)) ∈ idl V l.Mb := by
    rw [sub_mem_idl hι, liftLa_spec, liftLa_spec, liftLa_spec]
    rfl
  have := add_mem (add_mem (stab_idl h.1 (h'.2 a)) (h.2 (liftLa γ' a))) h3
  rw [Matrix.mulVec_sub, ← finHom_mul] at this
  convert this using 1
  abel

theorem nsmul_mem_idl {w : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E} (hw : w ∈ latGHat V 1) :
    l.M • w ∈ idl V l.Mb := by
  have := smul_mem_idl (M_mem l) hw
  rwa [iA_nat, Nat.cast_smul_eq_nsmul] at this

theorem ind_of_isLevLift (hι : LatEmb V ι) {γ : LevGrp Dw l} {κ : GA D V} (h : IsLevLift l V ι γ κ) :
    Ind V l ι γ κ := by
  have h1 : κ ∈ IndefiniteRowSideFullHecke.EmbeddingLevelSets.levSet V 1 := mem_levSet_one.2 ⟨h.1, fun z hz => by
    have : (finHom V κ).1 *ᵥ z ∈ gLat V κ := ⟨z, hz, rfl⟩
    rwa [h.2.1] at this⟩
  refine ⟨h1, fun a => ?_⟩
  obtain ⟨m, hm, c, hc, e⟩ := exists_split l
  have e0 : (l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)).mkQ (c • liftLa γ a) =
      γ ((l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)).mkQ (c • a)) := by
    rw [LinearMap.map_smul, LinearMap.map_smul, LinearEquiv.map_smul, liftLa_spec]
  obtain ⟨w, hw, e1⟩ := h.2.2 (c • a) (Submodule.smul_mem_smul hc Submodule.mem_top) (c • liftLa γ a)
    (Submodule.smul_mem_smul hc Submodule.mem_top) e0
  have h0 := nsmul_mem_idl (l := l) hw
  rw [← e1, ι.map_smul, ι.map_smul, finVec_smul, finVec_smul, Matrix.mulVec_smul, ← smul_sub] at h0
  have h2 := add_mem (smul_mem_idl hm (sub_mem (stab_latGHat h1 (iota_mem hι a)) (iota_mem hι (liftLa γ a)))) h0
  rw [← add_smul, ← iA_add, e, iA_one, one_smul] at h2
  exact h2

theorem Ind.isLevLift (hι : LatEmb V ι) {γ : LevGrp Dw l} {κ : GA D V} (h : Ind V l ι γ κ) :
    IsLevLift l V ι γ κ := by
  have h1 := mem_levSet_one.1 h.1
  refine ⟨h1.1, ?_, fun a ha a' ha' e => ?_⟩
  · refine Set.Subset.antisymm ?_ fun z hz => ⟨_, GlobalTheory.RecDict.finHom_inv_mulVec_mem V κ h1.2 z hz, ?_⟩
    · rintro _ ⟨z, hz, rfl⟩
      exact h1.2 z hz
    · show (finHom V κ).1 *ᵥ _ = z
      rw [← finHom_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.one_mulVec]
  · refine inf_idl l.prod l.coprime ?_ ?_
    · have := add_mem (h.2 a) ((sub_mem_idl hι (liftLa γ a) a').2 (by rw [liftLa_spec, e]))
      rwa [sub_add_sub_cancel] at this
    · exact sub_mem (stab_idl h.1 ((iota_mem_idl hι (Mc_ne l) a).2 ha)) ((iota_mem_idl hι (Mc_ne l) a').2 ha')

theorem ind_one_of (hι : LatEmb V ι) {κ : GA D V} (h1 : κ ∈ IndefiniteRowSideFullHecke.EmbeddingLevelSets.levSet V 1)
    (h : ∀ a, (finHom V κ).1 *ᵥ finVec V (ι a) - finVec V (ι a) ∈ idl V l.Mb) : Ind V l ι 1 κ := by
  refine ⟨h1, fun a => ?_⟩
  have := add_mem (h a) ((sub_mem_idl hι a (liftLa (1 : LevGrp Dw l) a)).2 (by rw [liftLa_spec]; rfl))
  rwa [sub_add_sub_cancel] at this

theorem ind_one_iff (hι : LatEmb V ι) {Kf : Subgroup (GA D V)} (hK : IsLevelK V l.M Kf) (hH : KfHalf V Kf l.M (Mc l))
    (κ : GA D V) : Ind V l ι 1 κ ↔ κ ∈ IndefiniteRowSideFullHecke.EmbeddingLevelSets.levSet V l.M := by
  constructor
  · intro h
    refine (hK κ).1 ((hH κ).2 ⟨h.1.1, ((GlobalTheory.Member.AALev.congruences_agree D V κ).2 l.M (Mc l)).2 fun a ha => ?_⟩)
    rw [← map_smul_top hι] at ha
    obtain ⟨a, ha, rfl⟩ := ha
    exact (h.isLevLift hι).2.2 a ha a ha rfl
  · intro h
    refine ind_one_of hι ⟨h.1, fun z hz => ?_⟩ fun a => ?_
    · obtain ⟨y, hy, e⟩ := h.2 z hz
      exact ⟨l.M • y, nsmul_mem hy _, by rw [one_smul, e]⟩
    · obtain ⟨w, hw, e⟩ := ((GlobalTheory.Member.AALev.congruences_agree D V κ).2 l.M ⊤).1
        (fun b _ z hz => h.2 _ (smul_mem_latHat (iA_mem b) hz)) (ι a)
        (by rw [Submodule.top_smul, ← hι.2]; exact LinearMap.mem_range_self ι a)
      exact e ▸ nsmul_mem_idl hw

end Lev

section Char

theorem ext_AE {z z' : AE D} (h1 : infPart D z = infPart D z') (h2 : finPart D z = finPart D z') : z = z' := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  exact e.injective (Prod.ext ((he z).1.trans (h1.trans (he z').1.symm)) ((he z).2.trans (h2.trans (he z').2.symm)))

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}

variable {ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)}

variable {χ : (AE D)ˣ →* Circle} {mu : GA D V → ℂ}

end Char

end GlobalTheory.UnifEvery
