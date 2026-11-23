import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.DistinguishedUnitIdeals.FinalArcProps

noncomputable section

namespace Formalism.MainNotions.WachCoordinates.Br

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem φD_smulA (T : LocLat G Qp LL O) (a : LetA O n) (x : W.DD T) :
    W.φD T (a • x) = W.φA a • W.φD T x := by
  show W.φD T (a • x) = (letφ W.φ₀ a) • W.φD T x
  rw [← algebraMap_smul W.EE a x, W.φD_smul, W.φE_ext, algebraMap_smul]

theorem γD_smulA (T : LocLat G Qp LL O) (g : W.Gam) (a : LetA O n) (x : W.DD T) :
    W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  show W.γD T g (a • x) = (letγ (W.γ₀ g) a) • W.γD T g x
  rw [← algebraMap_smul W.EE a x, W.γD_smul, W.γE_ext, algebraMap_smul]

theorem map_smulA {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) (a : LetA O n) (x : W.DD T) :
    W.map f (a • x) = a • W.map f x := by
  rw [← algebraMap_smul W.EE a x, map_smul, algebraMap_smul]

theorem φA_letE (i : ZMod n) : W.φA (letE (i - 1) : LetA O n) = letE i := by
  unfold Formalism.BasicNotions.LocWach.φA letφ letE
  funext j
  by_cases h : j = i <;> simp [Pi.single_apply, h, sub_left_inj]

theorem γA_letE (g : W.Gam) (i : ZMod n) : W.γA g (letE i : LetA O n) = letE i := by
  unfold Formalism.BasicNotions.LocWach.γA letγ letE
  funext j
  by_cases h : j = i <;> simp [Pi.single_apply, h]

theorem letE_mul_self (i : ZMod n) : (letE i : LetA O n) * letE i = letE i := by
  unfold letE LetA
  ext j
  by_cases h : j = i <;> simp [Pi.single_apply, h]

theorem letE_mul_ne {i k : ZMod n} (h : i ≠ k) : (letE i : LetA O n) * letE k = 0 := by
  unfold letE LetA
  ext j
  by_cases hj : j = i
  · subst hj; simp [Pi.single_apply, h]
  · simp [Pi.single_apply, hj]

theorem sum_letE [NeZero n] : ∑ i : ZMod n, (letE i : LetA O n) = 1 := by
  unfold letE LetA
  exact Finset.univ_sum_single (fun _ => (1 : PowerSeries O))

structure BaseId where
  Bs : Formalism.ExponentWindows.E.Base O
  ι : PowerSeries O →ₐ[O] PowerSeries O
  ι_X : ι PowerSeries.X = W.π₀₁
  ι_φ : ∀ a, ι (Bs.φ a) = W.φ₀ (ι a)
  ι_γ : ∀ a, ι (Bs.γ a) = W.γ₀ W.gamK (ι a)
  ι_Δ : ∀ δ ∈ W.DelF, ∀ a, W.γ₀ δ (ι a) = ι a
  ℓ_eq : Bs.ℓ = PD.p

variable {W}

def BaseId.d (I : BaseId W) : PowerSeries O →ₐ[O] LetA O n := AlgHom.pi fun _ => I.ι

@[simp] theorem BaseId.d_apply (I : BaseId W) (a : PowerSeries O) (i : ZMod n) : I.d a i = I.ι a := rfl

theorem BaseId.φA_d (I : BaseId W) (a : PowerSeries O) : W.φA (I.d a) = I.d (I.Bs.φ a) := by
  funext i
  show W.φ₀ (I.d a (i - 1)) = I.d (I.Bs.φ a) i
  rw [BaseId.d_apply, BaseId.d_apply, I.ι_φ]

theorem BaseId.γA_d (I : BaseId W) (a : PowerSeries O) : W.γA W.gamK (I.d a) = I.d (I.Bs.γ a) := by
  funext i
  show W.γ₀ W.gamK (I.d a i) = I.d (I.Bs.γ a) i
  rw [BaseId.d_apply, BaseId.d_apply, I.ι_γ]

theorem BaseId.γA_Δ (I : BaseId W) (δ : W.Gam) (hδ : δ ∈ W.DelF) (a : PowerSeries O) :
    W.γA δ (I.d a) = I.d a := by
  funext i
  show W.γ₀ δ (I.d a i) = I.d a i
  rw [BaseId.d_apply, I.ι_Δ δ hδ]

theorem BaseId.d_X (I : BaseId W) : I.d PowerSeries.X = W.π₀ := by
  funext i
  rw [BaseId.d_apply, I.ι_X]
  rfl

theorem BaseId.d_C (I : BaseId W) (m : O) : I.d (PowerSeries.C m) = algebraMap O (LetA O n) m := by
  rw [show PowerSeries.C m = algebraMap O (PowerSeries O) m from rfl]
  exact I.d.commutes m

theorem BaseId.d_q (I : BaseId W) : I.d I.Bs.q = qP W := by
  unfold Formalism.ExponentWindows.E.Base.q qP
  rw [map_add, I.d_X, I.d_C, I.ℓ_eq, map_natCast]

theorem BaseId.d_p (I : BaseId W) (s : ℕ) : I.d (I.Bs.p s) = pS W s := by
  unfold Formalism.ExponentWindows.E.Base.p pS
  induction s with
  | zero => simpa using I.d_q
  | succ s ih => rw [Function.iterate_succ_apply', ← I.φA_d, ih, pow_succ', AlgHom.mul_apply]

variable (W)

def DDl (T : LocLat G Qp LL O) (i : ZMod n) : AddSubgroup (W.DD T) where
  carrier := {x | (letE i : LetA O n) • x = x ∧ ∀ δ ∈ W.DelF, W.γD T δ x = x}
  zero_mem' := ⟨smul_zero _, fun δ _ => map_zero _⟩
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨by rw [smul_add, ha, hb], fun δ hδ => by rw [map_add, ha' δ hδ, hb' δ hδ]⟩
  neg_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨by rw [smul_neg, ha], fun δ hδ => by rw [map_neg, ha' δ hδ]⟩

def φl (T : LocLat G Qp LL O) (i : ZMod n) : ↥(DDl W T (i - 1)) →+ ↥(DDl W T i) where
  toFun x := ⟨W.φD T x, by
    refine ⟨?_, fun δ hδ => ?_⟩
    · rw [← φA_letE W i, ← φD_smulA, x.2.1]
    · rw [← W.φγ_comm, x.2.2 δ hδ]⟩
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

def γl (T : LocLat G Qp LL O) (g : W.Gam) (i : ZMod n) : ↥(DDl W T i) →+ ↥(DDl W T i) where
  toFun x := ⟨W.γD T g x, by
    refine ⟨?_, fun δ hδ => ?_⟩
    · conv_lhs => rw [← γA_letE W g i, ← γD_smulA, x.2.1]
    · rw [← W.γD_mul, mul_comm, W.γD_mul, x.2.2 δ hδ]⟩
  map_zero' := by ext; simp
  map_add' a b := by ext; simp

structure Coord (I : BaseId W) (T : LocLat G Qp LL O) where
  V : Type
  [acg : AddCommGroup V]
  [mod : Module (PowerSeries O) V]
  θ : ∀ i : ZMod n, V ≃+ ↥(DDl W T i)
  θ_smul : ∀ (i : ZMod n) (a : PowerSeries O) (x : V),
    ((θ i (a • x) : ↥(DDl W T i)) : W.DD T) = I.d a • ((θ i x : ↥(DDl W T i)) : W.DD T)

attribute [instance] Coord.acg Coord.mod

variable {W}
variable {I : BaseId W} {T : LocLat G Qp LL O}

def Coord.t (C : Coord W I T) (i : ZMod n) (x : C.V) : W.DD T := ((C.θ i x : ↥(DDl W T i)) : W.DD T)

theorem Coord.t_add (C : Coord W I T) (i : ZMod n) (x y : C.V) : C.t i (x + y) = C.t i x + C.t i y := by
  simp only [Coord.t, map_add, AddSubgroup.coe_add]

theorem Coord.t_sub (C : Coord W I T) (i : ZMod n) (x y : C.V) : C.t i (x - y) = C.t i x - C.t i y := by
  simp only [Coord.t, map_sub, AddSubgroup.coe_sub]

theorem Coord.t_zero (C : Coord W I T) (i : ZMod n) : C.t i 0 = 0 := by
  simp only [Coord.t, map_zero, ZeroMemClass.coe_zero]

theorem Coord.t_smul (C : Coord W I T) (i : ZMod n) (a : PowerSeries O) (x : C.V) :
    C.t i (a • x) = I.d a • C.t i x := C.θ_smul i a x

theorem Coord.t_inj (C : Coord W I T) (i : ZMod n) {x y : C.V} (h : C.t i x = C.t i y) : x = y :=
  (C.θ i).injective (Subtype.ext h)

theorem Coord.t_letter (C : Coord W I T) (i : ZMod n) (x : C.V) :
    (letE i : LetA O n) • C.t i x = C.t i x := (C.θ i x).2.1

theorem Coord.t_Δ (C : Coord W I T) (i : ZMod n) (x : C.V) (δ : W.Gam) (hδ : δ ∈ W.DelF) :
    W.γD T δ (C.t i x) = C.t i x := (C.θ i x).2.2 δ hδ

theorem Coord.t_surj (C : Coord W I T) (i : ZMod n) (x : W.DD T) (h1 : (letE i : LetA O n) • x = x)
    (h2 : ∀ δ ∈ W.DelF, W.γD T δ x = x) : ∃ y : C.V, C.t i y = x :=
  ⟨(C.θ i).symm ⟨x, h1, h2⟩, by simp only [Coord.t, AddEquiv.apply_symm_apply]⟩

def latOf (C : Coord W I T) : Formalism.ExponentWindows.E.Lat I.Bs n C.V where
  φ i := ((C.θ i).symm.toAddMonoidHom.comp (φl W T i)).comp (C.θ (i - 1)).toAddMonoidHom
  γ i := ((C.θ i).symm.toAddMonoidHom.comp (γl W T W.gamK i)).comp (C.θ i).toAddMonoidHom
  φ_semi i a x := by
    apply C.t_inj i
    rw [C.t_smul]
    simp only [Coord.t, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, AddEquiv.apply_symm_apply]
    change W.φD T (C.t (i - 1) (a • x)) = I.d (I.Bs.φ a) • W.φD T (C.t (i - 1) x)
    rw [C.t_smul, φD_smulA, I.φA_d]
  γ_semi i a x := by
    apply C.t_inj i
    rw [C.t_smul]
    simp only [Coord.t, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, AddEquiv.apply_symm_apply]
    change W.γD T W.gamK (C.t i (a • x)) = I.d (I.Bs.γ a) • W.γD T W.gamK (C.t i x)
    rw [C.t_smul, γD_smulA, I.γA_d]
  comm i x := by
    apply C.t_inj i
    simp only [Coord.t, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, AddEquiv.apply_symm_apply]
    change W.φD T (W.γD T W.gamK (C.t (i - 1) x)) = W.γD T W.gamK (W.φD T (C.t (i - 1) x))
    rw [W.φγ_comm]
  N i :=
    { carrier := {x | C.t i x ∈ W.N T}
      zero_mem' := by simp [C.t_zero]
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq, C.t_add] at *
        exact (W.N T).add_mem ha hb
      smul_mem' := by
        intro a x hx
        simp only [Set.mem_setOf_eq, C.t_smul] at *
        exact (W.N T).smul_mem _ hx }

theorem t_φ (C : Coord W I T) (i : ZMod n) (x : C.V) :
    C.t i ((latOf C).φ i x) = W.φD T (C.t (i - 1) x) := by
  simp only [Coord.t, latOf, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, AddEquiv.apply_symm_apply]
  rfl

theorem t_γ (C : Coord W I T) (i : ZMod n) (x : C.V) :
    C.t i ((latOf C).γ i x) = W.γD T W.gamK (C.t i x) := by
  simp only [Coord.t, latOf, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, AddEquiv.apply_symm_apply]
  rfl

theorem mem_N (C : Coord W I T) (i : ZMod n) (x : C.V) : x ∈ (latOf C).N i ↔ C.t i x ∈ W.N T := Iff.rfl

variable [NeZero n]

def tot (C : Coord W I T) (y : ZMod n → C.V) : W.DD T := ∑ i, C.t i (y i)

theorem tot_add (C : Coord W I T) (y z : ZMod n → C.V) : tot C (y + z) = tot C y + tot C z := by
  simp only [tot, Pi.add_apply, Coord.t_add, Finset.sum_add_distrib]

theorem tot_sub (C : Coord W I T) (y z : ZMod n → C.V) : tot C (y - z) = tot C y - tot C z := by
  simp only [tot, Pi.sub_apply, Coord.t_sub, Finset.sum_sub_distrib]

theorem tot_zero (C : Coord W I T) : tot C 0 = 0 := by
  simp only [tot, Pi.zero_apply, Coord.t_zero, Finset.sum_const_zero]

theorem tot_smul (C : Coord W I T) (a : PowerSeries O) (y : ZMod n → C.V) :
    tot C (a • y) = I.d a • tot C y := by
  simp only [tot, Pi.smul_apply, Coord.t_smul, Finset.smul_sum]

theorem tot_smulC (C : Coord W I T) (m : O) (y : ZMod n → C.V) :
    tot C (PowerSeries.C m • y) = m • tot C y := by
  rw [tot_smul, BaseId.d_C, algebraMap_smul]

theorem tot_Δ (C : Coord W I T) (y : ZMod n → C.V) (δ : W.Gam) (hδ : δ ∈ W.DelF) :
    W.γD T δ (tot C y) = tot C y := by
  rw [tot, map_sum]
  exact Finset.sum_congr rfl fun i _ => C.t_Δ i (y i) δ hδ

theorem letE_tot (C : Coord W I T) (y : ZMod n → C.V) (i : ZMod n) :
    (letE i : LetA O n) • tot C y = C.t i (y i) := by
  rw [tot, Finset.smul_sum, Finset.sum_eq_single i]
  · exact C.t_letter i (y i)
  · intro j _ hji
    rw [← C.t_letter j (y j), smul_smul, letE_mul_ne hji.symm, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem tot_inj (C : Coord W I T) {y z : ZMod n → C.V} (h : tot C y = tot C z) : y = z := by
  funext i
  apply C.t_inj i
  rw [← letE_tot, h, letE_tot]

theorem tot_surj (C : Coord W I T) (x : W.DD T) (hx : ∀ δ ∈ W.DelF, W.γD T δ x = x) :
    ∃ y : ZMod n → C.V, tot C y = x := by
  choose y hy using fun i => C.t_surj i ((letE i : LetA O n) • x)
    (by rw [smul_smul, letE_mul_self])
    (fun δ hδ => by rw [γD_smulA, γA_letE, hx δ hδ])
  refine ⟨y, ?_⟩
  simp only [tot, hy]
  rw [← Finset.sum_smul, sum_letE, one_smul]

theorem tot_dφ (C : Coord W I T) (z : ZMod n → C.V) :
    tot C ((latOf C).dφ z) = W.φD T (tot C z) - tot C z := by
  simp only [tot, Formalism.ExponentWindows.E.Lat.dφ, Coord.t_sub, t_φ, Finset.sum_sub_distrib, map_sum]
  congr 1
  exact Fintype.sum_equiv (Equiv.subRight 1) _ _ (fun i => rfl)

theorem tot_dγ (C : Coord W I T) (z : ZMod n → C.V) :
    tot C ((latOf C).dγ z) = W.γD T W.gamK (tot C z) - tot C z := by
  simp only [tot, Formalism.ExponentWindows.E.Lat.dγ, Coord.t_sub, t_γ, Finset.sum_sub_distrib, map_sum]

theorem mem_Z1DΔ (a b : W.DD T) : (a, b) ∈ W.wachCocyclesDelta T ↔
    W.γD T W.gamK a - a = W.φD T b - b ∧ (∀ δ ∈ W.DelF, W.γD T δ a = a) ∧
      ∀ δ ∈ W.DelF, W.γD T δ b = b := by
  unfold Formalism.BasicNotions.LocWach.wachCocyclesDelta herrZ1Δ herrCocycles
  simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.coprod_apply,
    LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.id_apply, LinearMap.prodMap_apply,
    Prod.mk_sub_mk, Prod.mk_eq_zero, sub_eq_zero]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, fun δ hδ => (h2 δ hδ).1, fun δ hδ => (h2 δ hδ).2⟩
    rwa [← sub_eq_add_neg, sub_eq_zero] at h1
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, fun δ hδ => ⟨h2 δ hδ, h3 δ hδ⟩⟩
    rw [← sub_eq_add_neg, sub_eq_zero]
    exact h1

theorem cocycle_iff (C : Coord W I T) (y z : ZMod n → C.V) :
    (latOf C).IsCocycle y z ↔ (tot C y, tot C z) ∈ W.wachCocyclesDelta T := by
  rw [mem_Z1DΔ]
  constructor
  · intro h
    refine ⟨?_, fun δ hδ => tot_Δ C y δ hδ, fun δ hδ => tot_Δ C z δ hδ⟩
    rw [← tot_dγ, ← tot_dφ]
    exact congrArg (tot C) h
  · rintro ⟨h, -, -⟩
    exact tot_inj C (by rw [tot_dγ, tot_dφ]; exact h)

def totP (C : Coord W I T) : ((ZMod n → C.V) × (ZMod n → C.V)) →+ W.DD T × W.DD T where
  toFun κ := (tot C κ.1, tot C κ.2)
  map_zero' := by simp [tot_zero]
  map_add' a b := by simp [tot_add]

def ZfD (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) : Submodule O (W.DD T × W.DD T) :=
  ((latticeFiniteCohomology PD T.L).comap (W.clK T)).map (W.wachCocyclesDelta T).subtype

def Zf (C : Coord W I T) : AddSubgroup ((ZMod n → C.V) × (ZMod n → C.V)) :=
  (ZfD W T).toAddSubgroup.comap (totP C)

theorem mem_Zf (C : Coord W I T) (κ : (ZMod n → C.V) × (ZMod n → C.V)) :
    κ ∈ Zf C ↔ ∃ w : ↥(W.wachCocyclesDelta T), W.clK T w ∈ latticeFiniteCohomology PD T.L ∧
      (w : W.DD T × W.DD T) = (tot C κ.1, tot C κ.2) := by
  constructor
  · rintro ⟨w, hw, he⟩
    exact ⟨w, hw, he⟩
  · rintro ⟨w, hw, he⟩
    exact ⟨w, hw, he⟩

theorem Zf_smul (C : Coord W I T) (m : O) (κ : (ZMod n → C.V) × (ZMod n → C.V)) (h : κ ∈ Zf C) :
    (PowerSeries.C m • κ.1, PowerSeries.C m • κ.2) ∈ Zf C := by
  rw [mem_Zf] at h ⊢
  obtain ⟨w, hw, he⟩ := h
  refine ⟨m • w, ?_, ?_⟩
  · have e : W.clK T (m • w) = m • W.clK T w := (W.clK T).map_smul m w
    rw [e]
    exact Submodule.smul_mem _ m hw
  · simp only [tot_smulC]
    rw [Submodule.coe_smul, he, Prod.smul_mk]

structure CoordHom {T T' : LocLat G Qp LL O} (C : Coord W I T) (C' : Coord W I T')
    (F : LatHom T.L T'.L) where
  f : C.V →ₗ[PowerSeries O] C'.V
  coord_hom_map_trace : ∀ (i : ZMod n) (x : C.V), C'.t i (f x) = W.map F (C.t i x)
  crys : IsCrys PD T.ρ
  crys' : IsCrys PD T'.ρ

def latHomOf {T T' : LocLat G Qp LL O} {C : Coord W I T} {C' : Coord W I T'} {F : LatHom T.L T'.L}
    (h : CoordHom C C' F) : Formalism.ExponentWindows.E.LatHom (latOf C) (latOf C') where
  f := h.f
  φ_comm i x := by
    apply C'.t_inj i
    rw [h.coord_hom_map_trace, t_φ, t_φ, h.coord_hom_map_trace, W.map_φ]
  γ_comm i x := by
    apply C'.t_inj i
    rw [h.coord_hom_map_trace, t_γ, t_γ, h.coord_hom_map_trace, W.map_γ]
  map_N i x hx := by
    rw [mem_N, h.coord_hom_map_trace]
    exact W.map_N F h.crys h.crys' _ hx

theorem tot_map {T T' : LocLat G Qp LL O} {C : Coord W I T} {C' : Coord W I T'} {F : LatHom T.L T'.L}
    (h : CoordHom C C' F) (y : ZMod n → C.V) :
    tot C' (fun i => (latHomOf h).f (y i)) = W.map F (tot C y) := by
  simp only [tot]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => h.coord_hom_map_trace i (y i)

def BaseId.Inj (I : BaseId W) : Prop := Function.Injective I.ι

def BaseId.Full (I : BaseId W) : Prop :=
  ∀ a : PowerSeries O, (∀ δ ∈ W.DelF, W.γ₀ δ a = a) → ∃ f : PowerSeries O, I.ι f = a

structure RealExt (C : Coord W I T) (C₀ : Coord W I W.one) where
  Y : LocLat G Qp LL O
  ι : LatHom T.L Y.L
  π : LatHom Y.L W.one.L
  CY : Coord W I Y
  hι : CoordHom C CY ι
  hπ : CoordHom CY C₀ π

def RealExt.Exact {C : Coord W I T} {C₀ : Coord W I W.one} (R : RealExt C C₀) : Prop :=
  Function.Injective R.hι.f ∧ ∀ x, R.hπ.f x = 0 ↔ ∃ u, R.hι.f u = x

def RealExt.ext {C : Coord W I T} {C₀ : Coord W I W.one} (R : RealExt C C₀) (h : R.Exact) :
    Formalism.ExponentWindows.E.Ext (latOf C) (latOf C₀) where
  VY := R.CY.V
  LY := latOf R.CY
  ι := latHomOf R.hι
  π := latHomOf R.hπ
  ι_inj := h.1
  exact := h.2

end Formalism.MainNotions.WachCoordinates.Br
