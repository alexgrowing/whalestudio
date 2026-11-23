import Formalism.SharpRestriction.LevelLetterCocycles.SaturationPullbackOfRingCondition
import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusPowUniformizerFactorisation

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.Relay2

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

open Formalism.MainNotions.UnusedSlot80.PhiPowers in
theorem φpow_smul (T : LocLat G Qp LL O) (k : ℕ) (a : LetA O n) (x : W.DD T) :
    ((W.φD T) ^ k) (a • x) = (W.φA ^ k) a • ((W.φD T) ^ k) x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_apply_succ, ih, φD_smulA, ← pow_apply_succ]
    congr 1
    rw [pow_succ', AlgHom.mul_apply]

open Formalism.MainNotions.UnusedSlot80.PhiPowers in
theorem γ_φpow (T : LocLat G Qp LL O) (g : W.Gam) (k : ℕ) (x : W.DD T) :
    W.γD T g (((W.φD T) ^ k) x) = ((W.φD T) ^ k) (W.γD T g x) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_apply_succ, ← W.φγ_comm, ih, ← pow_apply_succ]

theorem γA_comm' (g h : W.Gam) (a : LetA O n) : W.γA g (W.γA h a) = W.γA h (W.γA g a) := by
  rw [← Formalism.MainNotions.LiftingTheory.tr_γA_mul, mul_comm, Formalism.MainNotions.LiftingTheory.tr_γA_mul]

theorem γD_comm (T : LocLat G Qp LL O) (g h : W.Gam) (x : W.DD T) :
    W.γD T g (W.γD T h x) = W.γD T h (W.γD T g x) := by
  rw [← W.γD_mul, mul_comm, W.γD_mul]

theorem InNΔi_smul (T : LocLat G Qp LL O) (c : ZMod n) {a : LetA O n} (ha : a ∈ W.AΔ) {x : W.DD T}
    (hx : Formalism.MainNotions.LiftingTheory.InNΔi W T c x) : Formalism.MainNotions.LiftingTheory.InNΔi W T c (a • x) :=
  ⟨SatW.smul_mem_NΔ W T ha hx.1, (W.Nl T c).smul_mem a hx.2⟩

theorem InNΔi_add (T : LocLat G Qp LL O) (c : ZMod n) {x y : W.DD T}
    (hx : Formalism.MainNotions.LiftingTheory.InNΔi W T c x) (hy : Formalism.MainNotions.LiftingTheory.InNΔi W T c y) :
    Formalism.MainNotions.LiftingTheory.InNΔi W T c (x + y) :=
  ⟨(W.NΔ T).add_mem hx.1 hy.1, (W.Nl T c).add_mem hx.2 hy.2⟩

theorem InNΔi_osmul (T : LocLat G Qp LL O) (c : ZMod n) (o : O) {x : W.DD T}
    (hx : Formalism.MainNotions.LiftingTheory.InNΔi W T c x) : Formalism.MainNotions.LiftingTheory.InNΔi W T c (o • x) := by
  rw [← algebraMap_smul (LetA O n) o x]
  exact InNΔi_smul W T c ((W.AΔ).algebraMap_mem o) hx

theorem InNΔi_zero (T : LocLat G Qp LL O) (c : ZMod n) : Formalism.MainNotions.LiftingTheory.InNΔi W T c 0 :=
  ⟨(W.NΔ T).zero_mem, (W.Nl T c).zero_mem⟩

theorem InNΔi_sum (T : LocLat G Qp LL O) (c : ZMod n) {ι : Type} (s : Finset ι) (f : ι → W.DD T)
    (hf : ∀ i ∈ s, Formalism.MainNotions.LiftingTheory.InNΔi W T c (f i)) : Formalism.MainNotions.LiftingTheory.InNΔi W T c (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using InNΔi_zero W T c
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact InNΔi_add W T c (hf a (Finset.mem_insert_self _ _))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem InNΔi_letter (T : LocLat G Qp LL O) (c : ZMod n) {x : W.DD T}
    (hx : Formalism.MainNotions.LiftingTheory.InNΔi W T c x) : (letE c : LetA O n) • x = x := by
  obtain ⟨y, -, hy⟩ := hx.2
  rw [← hy, LinearMap.smul_apply, LinearMap.id_apply, smul_smul, letE_mul_self]

theorem InNΔi_of (T : LocLat G Qp LL O) (c : ZMod n) {x : W.DD T} (hx : x ∈ W.NΔ T)
    (hc : (letE c : LetA O n) • x = x) : Formalism.MainNotions.LiftingTheory.InNΔi W T c x :=
  ⟨hx, ⟨x, hx.1, by rw [LinearMap.smul_apply, LinearMap.id_apply, hc]⟩⟩

theorem InNΔi_γ (T : LocLat G Qp LL O) (c : ZMod n) {x : W.DD T}
    (hx : Formalism.MainNotions.LiftingTheory.InNΔi W T c x) : Formalism.MainNotions.LiftingTheory.InNΔi W T c (W.γ T x) := by
  refine InNΔi_of W T c ⟨W.N_Γ T W.gam x hx.1.1, fun δ hδ => ?_⟩ ?_
  · show W.γD T δ (W.γD T W.gam x) = W.γD T W.gam x
    rw [γD_comm, hx.1.2 δ hδ]
  · show (letE c : LetA O n) • W.γD T W.gam x = W.γD T W.gam x
    conv_rhs => rw [← InNΔi_letter W T c hx]
    rw [Formalism.MainNotions.LiftingTheory.frame_γD_smul, Formalism.MainNotions.LiftingTheory.frame_γA_letE]

theorem Pp_gen (T : LocLat G Qp LL O) (c : ZMod n) (e : ℕ) {a : LetA O n} (ha : a ∈ W.AΔ) {x : W.DD T}
    (hx : Formalism.MainNotions.LiftingTheory.InNΔi W T c x) : a • ((W.φD T) ^ e) x ∈ Formalism.MainNotions.ArcLiftingSetup.Pp W T c e :=
  AddSubgroup.subset_closure ⟨a, ha, x, hx, rfl⟩

theorem Pp_phi (T : LocLat G Qp LL O) (c : ZMod n) (e : ℕ) {x : W.DD T}
    (hx : Formalism.MainNotions.LiftingTheory.InNΔi W T c x) : ((W.φD T) ^ e) x ∈ Formalism.MainNotions.ArcLiftingSetup.Pp W T c e := by
  simpa using Pp_gen W T c e (W.AΔ.one_mem) hx

theorem Pp_ind (T : LocLat G Qp LL O) (c : ZMod n) (e : ℕ) (P : W.DD T → Prop)
    (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y)) (hneg : ∀ x, P x → P (-x))
    (hgen : ∀ a ∈ W.AΔ, ∀ x, Formalism.MainNotions.LiftingTheory.InNΔi W T c x → P (a • ((W.φD T) ^ e) x)) :
    ∀ y ∈ Formalism.MainNotions.ArcLiftingSetup.Pp W T c e, P y := by
  intro y hy
  induction hy using AddSubgroup.closure_induction with
  | mem z hz => obtain ⟨a, ha, x, hx, rfl⟩ := hz; exact hgen a ha x hx
  | zero => exact h0
  | add x y _ _ hx hy => exact hadd x y hx hy
  | neg x _ hx => exact hneg x hx

theorem Pp_smul (T : LocLat G Qp LL O) (c : ZMod n) (e : ℕ) {a : LetA O n} (ha : a ∈ W.AΔ) :
    ∀ y ∈ Formalism.MainNotions.ArcLiftingSetup.Pp W T c e, a • y ∈ Formalism.MainNotions.ArcLiftingSetup.Pp W T c e := by
  refine Pp_ind W T c e _ (by simpa using (Formalism.MainNotions.ArcLiftingSetup.Pp W T c e).zero_mem)
    (fun x y hx hy => by rw [smul_add]; exact (Formalism.MainNotions.ArcLiftingSetup.Pp W T c e).add_mem hx hy)
    (fun x hx => by rw [smul_neg]; exact (Formalism.MainNotions.ArcLiftingSetup.Pp W T c e).neg_mem hx) ?_
  intro b hb x hx
  rw [smul_smul]
  exact Pp_gen W T c e (W.AΔ.mul_mem ha hb) hx

theorem Pp_osmul (T : LocLat G Qp LL O) (c : ZMod n) (e : ℕ) (o : O) :
    ∀ y ∈ Formalism.MainNotions.ArcLiftingSetup.Pp W T c e, o • y ∈ Formalism.MainNotions.ArcLiftingSetup.Pp W T c e := by
  intro y hy
  rw [← algebraMap_smul (LetA O n) o y]
  exact Pp_smul W T c e ((W.AΔ).algebraMap_mem o) y hy

open Formalism.MainNotions.UnusedSlot80.PhiPowers in
theorem Pp_letter (T : LocLat G Qp LL O) (c : ZMod n) (e : ℕ) :
    ∀ y ∈ Formalism.MainNotions.ArcLiftingSetup.Pp W T c e, (letE (c + (e : ZMod n)) : LetA O n) • y = y := by
  refine Pp_ind W T c e _ (smul_zero _) (fun x y hx hy => by rw [smul_add, hx, hy])
    (fun x hx => by rw [smul_neg, hx]) ?_
  intro a _ x hx
  rw [smul_comm, φD_pow_letter W T c x (InNΔi_letter W T c hx) e]

open Formalism.MainNotions.UnusedSlot80.PhiPowers in
theorem Pp_Δ (T : LocLat G Qp LL O) (c : ZMod n) (e : ℕ) :
    ∀ y ∈ Formalism.MainNotions.ArcLiftingSetup.Pp W T c e, ∀ δ ∈ W.DelF, W.γD T δ y = y := by
  refine Pp_ind W T c e _ (fun δ _ => map_zero _)
    (fun x y hx hy δ hδ => by rw [map_add, hx δ hδ, hy δ hδ])
    (fun x hx δ hδ => by rw [map_neg, hx δ hδ]) ?_
  intro a ha x hx δ hδ
  rw [Formalism.MainNotions.LiftingTheory.frame_γD_smul, ha δ hδ, φD_pow_Δ W T hx.1.2 e δ hδ]

theorem Pp_γ (T : LocLat G Qp LL O) (c : ZMod n) (e : ℕ) :
    ∀ y ∈ Formalism.MainNotions.ArcLiftingSetup.Pp W T c e, W.γ T y ∈ Formalism.MainNotions.ArcLiftingSetup.Pp W T c e := by
  refine Pp_ind W T c e _ (by rw [map_zero]; exact (Formalism.MainNotions.ArcLiftingSetup.Pp W T c e).zero_mem)
    (fun x y hx hy => by rw [map_add]; exact (Formalism.MainNotions.ArcLiftingSetup.Pp W T c e).add_mem hx hy)
    (fun x hx => by rw [map_neg]; exact (Formalism.MainNotions.ArcLiftingSetup.Pp W T c e).neg_mem hx) ?_
  intro a ha x hx
  show W.γD T W.gam (a • ((W.φD T) ^ e) x) ∈ _
  rw [Formalism.MainNotions.LiftingTheory.frame_γD_smul, γ_φpow]
  exact Pp_gen W T c e (Formalism.MainNotions.LiftingTheory.tr_γA_mem W W.gam ha) (InNΔi_γ W T c hx)

theorem mapA_smul {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) (a : LetA O n) (x : W.DD T) :
    W.map f (a • x) = a • W.map f x := by
  rw [← algebraMap_smul W.EE a x, LinearMap.map_smul, algebraMap_smul]

theorem map_φpow {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) (k : ℕ) (x : W.DD T) :
    W.map f (((W.φD T) ^ k) x) = ((W.φD T') ^ k) (W.map f x) := by
  induction k with
  | zero => simp
  | succ k ih => rw [PhiPowers.pow_apply_succ, W.map_φ, ih, ← PhiPowers.pow_apply_succ]

theorem InNΔi_map {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) (hT : IsCrys PD T.ρ)
    (hT' : IsCrys PD T'.ρ) (c : ZMod n) {x : W.DD T}
    (hx : Formalism.MainNotions.LiftingTheory.InNΔi W T c x) : Formalism.MainNotions.LiftingTheory.InNΔi W T' c (W.map f x) := by
  refine InNΔi_of W T' c ⟨W.map_N f hT hT' x hx.1.1, fun δ hδ => ?_⟩ ?_
  · rw [← W.map_γ, hx.1.2 δ hδ]
  · rw [← mapA_smul, InNΔi_letter W T c hx]

theorem Pp_map {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) (hT : IsCrys PD T.ρ)
    (hT' : IsCrys PD T'.ρ) (c : ZMod n) (e : ℕ) :
    ∀ y ∈ Formalism.MainNotions.ArcLiftingSetup.Pp W T c e, W.map f y ∈ Formalism.MainNotions.ArcLiftingSetup.Pp W T' c e := by
  refine Pp_ind W T c e _ (by rw [map_zero]; exact (Formalism.MainNotions.ArcLiftingSetup.Pp W T' c e).zero_mem)
    (fun x y hx hy => by rw [map_add]; exact (Formalism.MainNotions.ArcLiftingSetup.Pp W T' c e).add_mem hx hy)
    (fun x hx => by rw [map_neg]; exact (Formalism.MainNotions.ArcLiftingSetup.Pp W T' c e).neg_mem hx) ?_
  intro a ha x hx
  rw [mapA_smul, map_φpow]
  exact Pp_gen W T' c e ha (InNΔi_map W f hT hT' c hx)

theorem inMultiple_of_mem (T : LocLat G Qp LL O) (c : ZMod n) (e : ℕ) (f : LetA O n) {y : W.DD T}
    (hy : y ∈ Formalism.MainNotions.ArcLiftingSetup.Pp W T c e) : Formalism.MainNotions.ArcLiftingSetup.InFP W T c e f (f • y) := ⟨y, hy, rfl⟩

theorem inMultiple_zero (T : LocLat G Qp LL O) (c : ZMod n) (e : ℕ) (f : LetA O n) :
    Formalism.MainNotions.ArcLiftingSetup.InFP W T c e f 0 := ⟨0, (Formalism.MainNotions.ArcLiftingSetup.Pp W T c e).zero_mem, (smul_zero _).symm⟩

theorem inMultiple_add (T : LocLat G Qp LL O) (c : ZMod n) (e : ℕ) (f : LetA O n) {x y : W.DD T}
    (hx : Formalism.MainNotions.ArcLiftingSetup.InFP W T c e f x) (hy : Formalism.MainNotions.ArcLiftingSetup.InFP W T c e f y) :
    Formalism.MainNotions.ArcLiftingSetup.InFP W T c e f (x + y) := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  exact ⟨a + b, (Formalism.MainNotions.ArcLiftingSetup.Pp W T c e).add_mem ha hb, (smul_add _ _ _).symm⟩

theorem inMultiple_neg (T : LocLat G Qp LL O) (c : ZMod n) (e : ℕ) (f : LetA O n) {x : W.DD T}
    (hx : Formalism.MainNotions.ArcLiftingSetup.InFP W T c e f x) : Formalism.MainNotions.ArcLiftingSetup.InFP W T c e f (-x) := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨-a, (Formalism.MainNotions.ArcLiftingSetup.Pp W T c e).neg_mem ha, (smul_neg _ _).symm⟩

theorem inMultiple_sub (T : LocLat G Qp LL O) (c : ZMod n) (e : ℕ) (f : LetA O n) {x y : W.DD T}
    (hx : Formalism.MainNotions.ArcLiftingSetup.InFP W T c e f x) (hy : Formalism.MainNotions.ArcLiftingSetup.InFP W T c e f y) :
    Formalism.MainNotions.ArcLiftingSetup.InFP W T c e f (x - y) := by
  rw [sub_eq_add_neg]; exact inMultiple_add W T c e f hx (inMultiple_neg W T c e f hy)

theorem inMultiple_smul (T : LocLat G Qp LL O) (c : ZMod n) (e : ℕ) (f : LetA O n) {a : LetA O n}
    (ha : a ∈ W.AΔ) {x : W.DD T} (hx : Formalism.MainNotions.ArcLiftingSetup.InFP W T c e f x) :
    Formalism.MainNotions.ArcLiftingSetup.InFP W T c e f (a • x) := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨a • y, Pp_smul W T c e ha y hy, smul_comm _ _ _⟩

theorem InFP_osmul (T : LocLat G Qp LL O) (c : ZMod n) (e : ℕ) (f : LetA O n) (o : O) {x : W.DD T}
    (hx : Formalism.MainNotions.ArcLiftingSetup.InFP W T c e f x) : Formalism.MainNotions.ArcLiftingSetup.InFP W T c e f (o • x) := by
  rw [← algebraMap_smul (LetA O n) o x]
  exact inMultiple_smul W T c e f ((W.AΔ).algebraMap_mem o) hx

theorem inMultiple_sum (T : LocLat G Qp LL O) (c : ZMod n) (e : ℕ) (f : LetA O n) {ι : Type}
    (s : Finset ι) (g : ι → W.DD T) (hg : ∀ i ∈ s, Formalism.MainNotions.ArcLiftingSetup.InFP W T c e f (g i)) :
    Formalism.MainNotions.ArcLiftingSetup.InFP W T c e f (∑ i ∈ s, g i) := by
  induction s using Finset.induction_on with
  | empty => simpa using inMultiple_zero W T c e f
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact inMultiple_add W T c e f (hg a (Finset.mem_insert_self _ _))
      (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))

theorem inMultiple_mul_smul (T : LocLat G Qp LL O) (c : ZMod n) (e : ℕ) (f g : LetA O n)
    {x : W.DD T} (hx : Formalism.MainNotions.ArcLiftingSetup.InFP W T c e f x) : Formalism.MainNotions.ArcLiftingSetup.InFP W T c e (g * f) (g • x) := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨y, hy, by rw [smul_smul]⟩

theorem mem_Pp_of_inMultiple (T : LocLat G Qp LL O) (c : ZMod n) (e : ℕ) {f : LetA O n} (hf : f ∈ W.AΔ)
    {x : W.DD T} (hx : Formalism.MainNotions.ArcLiftingSetup.InFP W T c e f x) : x ∈ Formalism.MainNotions.ArcLiftingSetup.Pp W T c e := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact Pp_smul W T c e hf y hy

theorem InFP_γ (T : LocLat G Qp LL O) (c : ZMod n) (e : ℕ) {f : LetA O n}
    (hf : ∃ u, W.γA W.gam f = u * f ∧ u ∈ W.AΔ) {x : W.DD T} (hx : Formalism.MainNotions.ArcLiftingSetup.InFP W T c e f x) :
    Formalism.MainNotions.ArcLiftingSetup.InFP W T c e f (W.γ T x) := by
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨u, hu, huΔ⟩ := hf
  refine ⟨u • W.γ T y, Pp_smul W T c e huΔ _ (Pp_γ W T c e y hy), ?_⟩
  show W.γD T W.gam (f • y) = _
  rw [Formalism.MainNotions.LiftingTheory.frame_γD_smul, hu, mul_comm, mul_smul]
  rfl

theorem inMultiple_map {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) (hT : IsCrys PD T.ρ)
    (hT' : IsCrys PD T'.ρ) (c : ZMod n) (e : ℕ) (g : LetA O n)
    {x : W.DD T} (hx : Formalism.MainNotions.ArcLiftingSetup.InFP W T c e g x) : Formalism.MainNotions.ArcLiftingSetup.InFP W T' c e g (W.map f x) := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨W.map f y, Pp_map W f hT hT' c e y hy, mapA_smul W f g y⟩

end Formalism.MainNotions.UnusedSlot80.Relay2

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.Relay2

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem lsmul_eq (T : LocLat G Qp LL O) (k : ℕ) (x : W.DD T) :
    ((PD.p : ℕ) : O) ^ k • x = Formalism.MainNotions.ArcLiftingSetup.lA W ^ k • x := by
  rw [Formalism.MainNotions.ArcLiftingSetup.lA, ← Nat.cast_pow, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]

theorem γ_lsmul (T : LocLat G Qp LL O) (k : ℕ) (x : W.DD T) :
    W.γ T (Formalism.MainNotions.ArcLiftingSetup.lA W ^ k • x) = Formalism.MainNotions.ArcLiftingSetup.lA W ^ k • W.γ T x := by
  rw [← lsmul_eq, ← lsmul_eq, map_smul]

theorem φpow_lsmul (T : LocLat G Qp LL O) (e k : ℕ) (x : W.DD T) :
    ((W.φD T) ^ e) (Formalism.MainNotions.ArcLiftingSetup.lA W ^ k • x) = Formalism.MainNotions.ArcLiftingSetup.lA W ^ k • ((W.φD T) ^ e) x := by
  rw [← lsmul_eq, ← lsmul_eq, map_smul]

theorem frame_exists (T : LocLat G Qp LL O) (c : ZMod n) (hm : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀) :
    ∃ (d : ℕ) (b : Fin d → W.DD T), Formalism.MainNotions.LiftingTheory.IsFrameΔ W T c b := by
  obtain ⟨⟨r, b, hb, huniq, hΔ⟩, -⟩ := hm
  have hE := Formalism.MainNotions.LiftingTheory.idempotent_mem_invariants W c
  refine ⟨r, fun m => (letE c : LetA O n) • b m, fun m => ?_, fun x hx => ?_⟩
  · refine InNΔi_of W T c (SatW.smul_mem_NΔ W T hE (hb m)) ?_
    rw [smul_smul, letE_mul_self]
  · obtain ⟨a, haΔ, ha⟩ := hΔ x hx.1
    have hxc := InNΔi_letter W T c hx
    refine ⟨fun m => (letE c : LetA O n) * a m, ⟨fun m => ⟨W.AΔ.mul_mem hE (haΔ m), ?_⟩, ?_⟩, ?_⟩
    · rw [← mul_assoc, letE_mul_self]
    · conv_lhs => rw [← hxc, ha, Finset.smul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [smul_smul, smul_smul, mul_assoc, mul_comm (a m), ← mul_assoc, letE_mul_self]
    · rintro a' ⟨ha'1, ha'2⟩
      obtain ⟨a0, -, hu⟩ := huniq x hx.1.1
      have e1 : x = ∑ m, (a' m * letE c) • b m := by
        rw [ha'2]; simp only [smul_smul]
      have e2 : x = ∑ m, ((letE c * a m) * letE c) • b m := by
        conv_lhs => rw [← hxc, ha, Finset.smul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [smul_smul, mul_comm (letE c * a m), ← mul_assoc, letE_mul_self]
      funext m
      have := congrFun ((hu _ e1).trans (hu _ e2).symm) m
      rw [mul_comm (a' m), (ha'1 m).2, mul_comm _ (letE c), ← mul_assoc, letE_mul_self] at this
      rw [this]

theorem pk_mem_AΔ (hπ : W.π₀ ∈ W.AΔ) (k : ℕ) : Formalism.MainNotions.LiftingTheory.pk W k ∈ W.AΔ :=
  PhiPowers.φA_pow_mem_AΔ W (W.AΔ.add_mem hπ (W.AΔ.natCast_mem _)) k

theorem phij_pi0pow (T : LocLat G Qp LL O) (c : ZMod n) (hπ : W.π₀ ∈ W.AΔ)
    (h2 : ∀ j r : ℕ, ∃ u ∈ W.AΔ, ∃ u' ∈ W.AΔ, u * u' = 1 ∧
      ((W.φA ^ j) W.π₀) ^ r = u * W.π₀ ^ r * ∏ k ∈ Finset.range j, Formalism.MainNotions.LiftingTheory.pk W k ^ ((PD.p - 1) * r))
    (j y M : ℕ) (hM : y ≤ (PD.p - 1) * M) {x : W.DD T} (hx : Formalism.MainNotions.LiftingTheory.InNΔi W T c x) :
    Formalism.MainNotions.ArcLiftingSetup.InFP W T c j (Formalism.MainNotions.LiftingTheory.JJ W j y M) (((W.φD T) ^ j) (W.π₀ ^ M • x)) := by
  obtain ⟨u, hu, -, -, -, hj⟩ := h2 j M
  rw [φpow_smul, map_pow, hj]
  have e : u * W.π₀ ^ M * ∏ k ∈ Finset.range j, Formalism.MainNotions.LiftingTheory.pk W k ^ ((PD.p - 1) * M) =
      Formalism.MainNotions.LiftingTheory.JJ W j y M * (u * ∏ k ∈ Finset.range j, Formalism.MainNotions.LiftingTheory.pk W k ^ ((PD.p - 1) * M - y)) := by
    rw [Formalism.MainNotions.LiftingTheory.JJ]
    have : ∀ k ∈ Finset.range j, Formalism.MainNotions.LiftingTheory.pk W k ^ ((PD.p - 1) * M) =
        Formalism.MainNotions.LiftingTheory.pk W k ^ y * Formalism.MainNotions.LiftingTheory.pk W k ^ ((PD.p - 1) * M - y) := fun k _ => by
      rw [← pow_add]; congr 1; omega
    rw [Finset.prod_congr rfl this, Finset.prod_mul_distrib]
    ring
  rw [e, mul_smul]
  refine inMultiple_of_mem W T c j _ (Pp_gen W T c j ?_ hx)
  exact W.AΔ.mul_mem hu (W.AΔ.prod_mem fun k _ => W.AΔ.pow_mem (pk_mem_AΔ W hπ k) _)

theorem principal_unit_pow_sub_one_dvd (hinj : Function.Injective (algebraMap O LL))
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x) (r : ℕ)
    (hv : v (algebraMap O LL (Formalism.MainNotions.LiftingTheory.u₁ W ^ r - 1)) = ((1 + padicValNat PD.p r : ℕ) : WithTop ℚ)) :
    ∃ e : O, e * (Formalism.MainNotions.LiftingTheory.u₁ W ^ r - 1) = ((PD.p : ℕ) : O) ^ (1 + padicValNat PD.p r) := by
  set t := 1 + padicValNat PD.p r
  set u := algebraMap O LL (Formalism.MainNotions.LiftingTheory.u₁ W ^ r - 1)
  have hu0 : u ≠ 0 := by
    intro h; rw [h, AddValuation.map_zero] at hv; exact WithTop.top_ne_coe hv
  have hvl : v ((PD.p : LL) ^ t) = ((t : ℕ) : WithTop ℚ) := by
    rw [AddValuation.map_pow, W.v_l, nsmul_one]
  have h0 : 0 ≤ v ((PD.p : LL) ^ t * u⁻¹) := by
    have hmul := v.map_mul ((PD.p : LL) ^ t * u⁻¹) u
    rw [inv_mul_cancel_right₀ hu0, hvl, hv] at hmul
    rcases hx : v ((PD.p : LL) ^ t * u⁻¹) with _ | q
    · exact le_top
    · rw [hx] at hmul
      have h' : (((t : ℕ) : ℚ) : WithTop ℚ) = ((q + ((t : ℕ) : ℚ) : ℚ) : WithTop ℚ) := by
        rw [WithTop.coe_add, WithTop.coe_natCast]; exact hmul
      have h'' := WithTop.coe_injective h'
      have hq : q = 0 := by linarith
      rw [hq]; rfl
  obtain ⟨e, he⟩ := hO2 _ h0
  refine ⟨e, hinj ?_⟩
  rw [map_mul, he, map_pow, map_natCast, inv_mul_cancel_right₀ hu0]

theorem alg_step {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (π a P : A) (x x' z Y : M)
    (r m : ℕ) (h : Y = a • (π ^ r • x) + π ^ (r + 1) • x') (h' : Y = P • ((π ^ r * π * π ^ m) • z)) :
    π ^ r • (a • x - π • (π ^ m • (P • z) - x')) = 0 := by
  have e := h.symm.trans h'
  linear_combination (norm := module) e

theorem formal_unique (T : LocLat G Qp LL O) (c : ZMod n)
    (hinj : Function.Injective (algebraMap O LL))
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x) (hπ : W.π₀ ∈ W.AΔ)
    (hw : ∃ w : (LetA O n)ˣ, W.π₀ = (w : LetA O n) * letπ ^ (PD.p - 1))
    (h1 : ∀ (r : ℕ) (x : W.DD T), Formalism.MainNotions.LiftingTheory.InNΔi W T c x → ∃ x', Formalism.MainNotions.LiftingTheory.InNΔi W T c x' ∧
      W.γ T (W.π₀ ^ r • x) - W.π₀ ^ r • x = (Formalism.MainNotions.LiftingTheory.u₁ W ^ r - 1) • (W.π₀ ^ r • x) +
        W.π₀ ^ (r + 1) • x')
    (h2 : ∀ r : ℕ, 1 ≤ r →
      v (algebraMap O LL (Formalism.MainNotions.LiftingTheory.u₁ W ^ r - 1)) = ((1 + padicValNat PD.p r : ℕ) : WithTop ℚ))
    (R : ℕ) (E : W.DD T) (hE : ∃ E', Formalism.MainNotions.LiftingTheory.InNΔi W T c E' ∧ E = W.π₀ • E')
    (hγ : ∃ z, Formalism.MainNotions.LiftingTheory.InNΔi W T c z ∧ W.γ T E - E = W.π₀ ^ R • z) :
    ∃ (k : ℕ) (x : W.DD T), Formalism.MainNotions.LiftingTheory.InNΔi W T c x ∧ Formalism.MainNotions.ArcLiftingSetup.lA W ^ k • E = W.π₀ ^ R • x := by
  obtain ⟨z, hz, hzE⟩ := hγ
  have key : ∀ r, 1 ≤ r → r ≤ R → ∃ (k : ℕ) (x : W.DD T), Formalism.MainNotions.LiftingTheory.InNΔi W T c x ∧
      Formalism.MainNotions.ArcLiftingSetup.lA W ^ k • E = W.π₀ ^ r • x := by
    intro r hr1
    induction r with
    | zero => omega
    | succ r ih =>
      intro hrR
      rcases Nat.eq_zero_or_pos r with h0 | hpos
      · subst h0; obtain ⟨E', hE', rfl⟩ := hE; exact ⟨0, E', hE', by simp⟩
      obtain ⟨k, x, hx, hkx⟩ := ih hpos (by omega)
      obtain ⟨x', hx', h1x⟩ := h1 r x hx
      obtain ⟨e, he⟩ := principal_unit_pow_sub_one_dvd W hinj hO2 r (h2 r hpos)
      set a : LetA O n := algebraMap O (LetA O n) (Formalism.MainNotions.LiftingTheory.u₁ W ^ r - 1) with ha
      have e1 : W.γ T (W.π₀ ^ r • x) - W.π₀ ^ r • x = Formalism.MainNotions.ArcLiftingSetup.lA W ^ k • (W.π₀ ^ R • z) := by
        rw [← hkx, γ_lsmul, ← smul_sub, hzE]
      rw [← algebraMap_smul (LetA O n) (Formalism.MainNotions.LiftingTheory.u₁ W ^ r - 1), ← ha, e1] at h1x
      have hR : W.π₀ ^ R = W.π₀ ^ r * W.π₀ * W.π₀ ^ (R - (r + 1)) := by
        rw [← pow_succ, ← pow_add]; congr 1; omega
      set y := W.π₀ ^ (R - (r + 1)) • (Formalism.MainNotions.ArcLiftingSetup.lA W ^ k • z) - x' with hy
      have h3 : W.π₀ ^ r • (a • x - W.π₀ • y) = 0 := by
        rw [hR] at h1x
        rw [hy]
        exact alg_step _ _ _ _ _ _ _ _ _ h1x rfl
      have h4 := Formalism.MainNotions.LiftingTheory.frame_π₀_inj W T hw r _ h3
      rw [sub_eq_zero] at h4
      have hyN : Formalism.MainNotions.LiftingTheory.InNΔi W T c y := by
        rw [hy, sub_eq_add_neg, ← neg_one_smul O x', ← lsmul_eq]
        exact InNΔi_add W T c (InNΔi_smul W T c (W.AΔ.pow_mem hπ _) (InNΔi_osmul W T c _ hz))
          (InNΔi_osmul W T c _ hx')
      refine ⟨k + (1 + padicValNat PD.p r), e • y, InNΔi_osmul W T c e hyN, ?_⟩
      rw [pow_add, mul_smul, smul_comm, hkx, ← lsmul_eq, smul_comm, ← he, mul_smul,
        ← algebraMap_smul (LetA O n) (Formalism.MainNotions.LiftingTheory.u₁ W ^ r - 1) x, ← ha, h4, smul_comm e, pow_succ,
        mul_smul]
  rcases Nat.eq_zero_or_pos R with h0 | hpos
  · subst h0
    obtain ⟨E', hE', rfl⟩ := hE
    exact ⟨0, W.π₀ • E', InNΔi_smul W T c hπ hE', by simp⟩
  · exact key R hpos le_rfl

theorem JJ_mem_PiPs (j y M : ℕ) : Formalism.MainNotions.LiftingTheory.JJ W j y M ∈ Formalism.MainNotions.ArcLiftingSetup.PiPs W := by
  have h0 : W.π₀ ∈ Formalism.MainNotions.ArcLiftingSetup.PiPs W := Submonoid.subset_closure (Set.mem_insert _ _)
  have h1 : ∀ k, Formalism.MainNotions.LiftingTheory.pk W k ∈ Formalism.MainNotions.ArcLiftingSetup.PiPs W := fun k =>
    Submonoid.subset_closure (Set.mem_insert_of_mem _ (Set.mem_range_self (f := Formalism.MainNotions.ArcLiftingSetup.ps W) k))
  exact Submonoid.mul_mem _ (Submonoid.pow_mem _ h0 _)
    (Submonoid.prod_mem _ fun k _ => Submonoid.pow_mem _ (h1 k) _)

theorem satP_JJ (hsp : Formalism.MainNotions.ArcLiftingSetup.SATPcore W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (hπ : W.π₀ ∈ W.AΔ)
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (c : ZMod n) (j y M : ℕ) (x : W.DD T)
    (hx : x ∈ Formalism.MainNotions.ArcLiftingSetup.Pp W T c j) (k : ℕ)
    (hk : Formalism.MainNotions.ArcLiftingSetup.InFP W T c j (Formalism.MainNotions.LiftingTheory.JJ W j y M) (Formalism.MainNotions.ArcLiftingSetup.lA W ^ k • x)) :
    Formalism.MainNotions.ArcLiftingSetup.InFP W T c j (Formalism.MainNotions.LiftingTheory.JJ W j y M) x := by
  refine hsp hA T c j _ 1 hT ?_ (Submonoid.one_mem _) x ⟨x, hx, by simp⟩ ⟨k, hk⟩
  exact JJ_mem_PiPs W j y M

end Formalism.MainNotions.UnusedSlot80.Relay2

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.Relay2

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

section Alg

variable {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]

theorem lin_add (L π : A) (a b m : ℕ) (g₁ s₁ z₁ x₁ g₂ s₂ z₂ x₂ : M)
    (e₁ : g₁ - s₁ - L ^ a • z₁ = π ^ m • x₁) (e₂ : g₂ - s₂ - L ^ b • z₂ = π ^ m • x₂) :
    L ^ b • g₁ + L ^ a • g₂ - (L ^ b • s₁ + L ^ a • s₂) - L ^ (a + b) • (z₁ + z₂) =
      π ^ m • (L ^ b • x₁ + L ^ a • x₂) := by
  linear_combination (norm := module) L ^ b • e₁ + L ^ a • e₂

theorem lin_scale (L π : A) (a k m : ℕ) (g s z x : M) (e : g - s - L ^ a • z = π ^ m • x) :
    L ^ k • g - L ^ k • s - L ^ (a + k) • z = π ^ m • (L ^ k • x) := by
  linear_combination (norm := module) L ^ k • e

theorem lin_cong (L π : A) (a m : ℕ) (g₁ s₁ x₁ g₂ s₂ x₂ z : M)
    (e₁ : g₁ - s₁ - L ^ a • z = π ^ m • x₁) (e₂ : g₂ - s₂ - L ^ a • z = π ^ m • x₂) :
    g₁ - g₂ - (s₁ - s₂) = π ^ m • (x₁ - x₂) := by
  linear_combination (norm := module) e₁ - e₂

theorem lin_gadd (L : A) (k₁ k₂ k₁' k₂' σ : ℕ) (τ₁ τ₂ p₁ p₂ : M) :
    L ^ (k₁' + k₂') • (L ^ (k₁ + k₂) • (τ₁ + τ₂) - L ^ σ • (L ^ k₂ • p₁ + L ^ k₁ • p₂)) =
      L ^ (k₂' + k₂) • (L ^ k₁' • (L ^ k₁ • τ₁ - L ^ σ • p₁)) +
        L ^ (k₁' + k₁) • (L ^ k₂' • (L ^ k₂ • τ₂ - L ^ σ • p₂)) := by
  module

theorem lin_gcong (L : A) (K k₁ k₂ k₁' k₂' σ : ℕ) (τ τ' p₁ p₂ : M) :
    L ^ (K + k₁' + k₂' + k₁ + k₂) • (τ - τ') =
      L ^ (K + k₂' + k₂) • (L ^ k₁' • (L ^ k₁ • τ - L ^ σ • p₁)) +
        L ^ (k₁' + k₂' + σ) • (L ^ K • (L ^ k₂ • p₁ - L ^ k₁ • p₂)) -
        L ^ (K + k₁' + k₁) • (L ^ k₂' • (L ^ k₂ • τ' - L ^ σ • p₂)) := by
  module

theorem lin_gto (L : A) (K k₁ k₂ k₁' σ : ℕ) (τ p₁ p₂ : M) :
    L ^ (K + k₁' + k₁) • (L ^ k₂ • τ - L ^ σ • p₂) =
      L ^ (K + k₂) • (L ^ k₁' • (L ^ k₁ • τ - L ^ σ • p₁)) +
        L ^ (k₁' + σ) • (L ^ K • (L ^ k₂ • p₁ - L ^ k₁ • p₂)) := by
  module

end Alg

structure Ctx (T : LocLat G Qp LL O) : Prop where
  inj : Function.Injective (algebraMap O LL)
  O2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x
  hπ : W.π₀ ∈ W.AΔ
  hw : ∃ w : (LetA O n)ˣ, W.π₀ = (w : LetA O n) * letπ ^ (PD.p - 1)
  H1 : ∀ (i : ZMod n) (r : ℕ) (x : W.DD T), Formalism.MainNotions.LiftingTheory.InNΔi W T i x → ∃ x', Formalism.MainNotions.LiftingTheory.InNΔi W T i x' ∧
      W.γ T (W.π₀ ^ r • x) - W.π₀ ^ r • x = (Formalism.MainNotions.LiftingTheory.u₁ W ^ r - 1) • (W.π₀ ^ r • x) +
        W.π₀ ^ (r + 1) • x'
  H2 : ∀ r : ℕ, 1 ≤ r →
      v (algebraMap O LL (Formalism.MainNotions.LiftingTheory.u₁ W ^ r - 1)) = ((1 + padicValNat PD.p r : ℕ) : WithTop ℚ)
  Tr2 : ∀ j r : ℕ, ∃ u ∈ W.AΔ, ∃ u' ∈ W.AΔ, u * u' = 1 ∧
      ((W.φA ^ j) W.π₀) ^ r = u * W.π₀ ^ r * ∏ k ∈ Finset.range j, Formalism.MainNotions.LiftingTheory.pk W k ^ ((PD.p - 1) * r)

def SolOK (T : LocLat G Qp LL O) (c : ZMod n) (M : ℕ) (Z : W.DD T) (κ : ℕ) (S : W.DD T) : Prop :=
  (∃ S', Formalism.MainNotions.LiftingTheory.InNΔi W T c S' ∧ S = W.π₀ • S') ∧
    ∃ x, Formalism.MainNotions.LiftingTheory.InNΔi W T c x ∧ W.γ T S - S - Formalism.MainNotions.ArcLiftingSetup.lA W ^ κ • Z = W.π₀ ^ M • x

def Good (T : LocLat G Qp LL O) (c : ZMod n) (j y M σ : ℕ) (w τ : W.DD T) : Prop :=
  ∃ κ κ' S, SolOK W T c M (W.γ T w - w) κ S ∧
    Formalism.MainNotions.ArcLiftingSetup.InFP W T c j (Formalism.MainNotions.LiftingTheory.JJ W j y M)
      (Formalism.MainNotions.ArcLiftingSetup.lA W ^ κ' • (Formalism.MainNotions.ArcLiftingSetup.lA W ^ κ • τ - Formalism.MainNotions.ArcLiftingSetup.lA W ^ σ • ((W.φD T) ^ j) S))

theorem lA_mem : Formalism.MainNotions.ArcLiftingSetup.lA W ∈ W.AΔ := W.AΔ.natCast_mem _

theorem InNΔi_lsmul (T : LocLat G Qp LL O) (c : ZMod n) (k : ℕ) {x : W.DD T}
    (hx : Formalism.MainNotions.LiftingTheory.InNΔi W T c x) : Formalism.MainNotions.LiftingTheory.InNΔi W T c (Formalism.MainNotions.ArcLiftingSetup.lA W ^ k • x) :=
  InNΔi_smul W T c (W.AΔ.pow_mem (lA_mem W) k) hx

theorem InNΔi_sub (T : LocLat G Qp LL O) (c : ZMod n) {x y : W.DD T}
    (hx : Formalism.MainNotions.LiftingTheory.InNΔi W T c x) (hy : Formalism.MainNotions.LiftingTheory.InNΔi W T c y) :
    Formalism.MainNotions.LiftingTheory.InNΔi W T c (x - y) := by
  rw [sub_eq_add_neg, ← neg_one_smul O y]
  exact InNΔi_add W T c hx (InNΔi_osmul W T c _ hy)

theorem inMultiple_lA_pow_smul (T : LocLat G Qp LL O) (c : ZMod n) (e : ℕ) (f : LetA O n) (k : ℕ) {x : W.DD T}
    (hx : Formalism.MainNotions.ArcLiftingSetup.InFP W T c e f x) : Formalism.MainNotions.ArcLiftingSetup.InFP W T c e f (Formalism.MainNotions.ArcLiftingSetup.lA W ^ k • x) :=
  inMultiple_smul W T c e f (W.AΔ.pow_mem (lA_mem W) k) hx

theorem solOK_add (T : LocLat G Qp LL O) (c : ZMod n) (M : ℕ) {Z₁ Z₂ S₁ S₂ : W.DD T} {κ₁ κ₂ : ℕ}
    (h₁ : SolOK W T c M Z₁ κ₁ S₁) (h₂ : SolOK W T c M Z₂ κ₂ S₂) :
    SolOK W T c M (Z₁ + Z₂) (κ₁ + κ₂)
      (Formalism.MainNotions.ArcLiftingSetup.lA W ^ κ₂ • S₁ + Formalism.MainNotions.ArcLiftingSetup.lA W ^ κ₁ • S₂) := by
  obtain ⟨⟨S₁', hS₁', rfl⟩, x₁, hx₁, e₁⟩ := h₁
  obtain ⟨⟨S₂', hS₂', rfl⟩, x₂, hx₂, e₂⟩ := h₂
  refine ⟨⟨_, InNΔi_add W T c (InNΔi_lsmul W T c κ₂ hS₁') (InNΔi_lsmul W T c κ₁ hS₂'), ?_⟩,
    _, InNΔi_add W T c (InNΔi_lsmul W T c κ₂ hx₁) (InNΔi_lsmul W T c κ₁ hx₂), ?_⟩
  · simp only [smul_add, smul_comm W.π₀]
  · rw [map_add, γ_lsmul, γ_lsmul]
    exact lin_add _ _ _ _ _ _ _ _ _ _ _ _ _ e₁ e₂

theorem solOK_scale (T : LocLat G Qp LL O) (c : ZMod n) (M : ℕ) {Z S : W.DD T} {κ : ℕ} (k : ℕ)
    (h : SolOK W T c M Z κ S) : SolOK W T c M Z (κ + k) (Formalism.MainNotions.ArcLiftingSetup.lA W ^ k • S) := by
  obtain ⟨⟨S', hS', rfl⟩, x, hx, e⟩ := h
  refine ⟨⟨_, InNΔi_lsmul W T c k hS', smul_comm _ _ _⟩, _, InNΔi_lsmul W T c k hx, ?_⟩
  rw [γ_lsmul]
  exact lin_scale _ _ _ _ _ _ _ _ _ e

theorem solOK_map {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) (hT : IsCrys PD T.ρ)
    (hT' : IsCrys PD T'.ρ) (c : ZMod n) (M : ℕ) {Z S : W.DD T}
    {κ : ℕ} (h : SolOK W T c M Z κ S) : SolOK W T' c M (W.map f Z) κ (W.map f S) := by
  obtain ⟨⟨S', hS', rfl⟩, x, hx, e⟩ := h
  refine ⟨⟨_, InNΔi_map W f hT hT' c hS', mapA_smul W f _ _⟩, _, InNΔi_map W f hT hT' c hx, ?_⟩
  have := congrArg (W.map f) e
  rw [map_sub, map_sub, mapA_smul, mapA_smul] at this
  rw [show W.γ T' (W.map f (W.π₀ • S')) = W.map f (W.γ T (W.π₀ • S')) from (W.map_γ f W.gam _).symm,
    mapA_smul W f W.π₀ S', ← mapA_smul W f (W.π₀ ^ M) x]
  exact this

theorem solOK_cong (T : LocLat G Qp LL O) (hC : Ctx W T) (c : ZMod n) (j y M : ℕ)
    (hM : y ≤ (PD.p - 1) * M) {Z S₁ S₂ : W.DD T} {κ : ℕ}
    (h₁ : SolOK W T c M Z κ S₁) (h₂ : SolOK W T c M Z κ S₂) :
    ∃ K, Formalism.MainNotions.ArcLiftingSetup.InFP W T c j (Formalism.MainNotions.LiftingTheory.JJ W j y M)
      (Formalism.MainNotions.ArcLiftingSetup.lA W ^ K • (((W.φD T) ^ j) S₁ - ((W.φD T) ^ j) S₂)) := by
  obtain ⟨⟨S₁', hS₁', rfl⟩, x₁, hx₁, e₁⟩ := h₁
  obtain ⟨⟨S₂', hS₂', rfl⟩, x₂, hx₂, e₂⟩ := h₂
  obtain ⟨K, x, hx, hK⟩ := formal_unique W T c hC.inj hC.O2 hC.hπ hC.hw (hC.H1 c) hC.H2 M
    (W.π₀ • S₁' - W.π₀ • S₂') ⟨S₁' - S₂', InNΔi_sub W T c hS₁' hS₂', (smul_sub _ _ _).symm⟩
    ⟨x₁ - x₂, InNΔi_sub W T c hx₁ hx₂, by
      rw [map_sub]; exact lin_cong _ _ _ _ _ _ _ _ _ _ _ e₁ e₂⟩
  refine ⟨K, ?_⟩
  rw [← map_sub, ← φpow_lsmul, hK]
  exact phij_pi0pow W T c hC.hπ hC.Tr2 j y M hM hx

theorem good_add (T : LocLat G Qp LL O) (c : ZMod n) (j y M σ : ℕ) {w₁ w₂ τ₁ τ₂ : W.DD T}
    (h₁ : Good W T c j y M σ w₁ τ₁) (h₂ : Good W T c j y M σ w₂ τ₂) :
    Good W T c j y M σ (w₁ + w₂) (τ₁ + τ₂) := by
  obtain ⟨κ₁, κ₁', S₁, hS₁, hX₁⟩ := h₁
  obtain ⟨κ₂, κ₂', S₂, hS₂, hX₂⟩ := h₂
  have hS := solOK_add W T c M hS₁ hS₂
  have e : W.γ T (w₁ + w₂) - (w₁ + w₂) = (W.γ T w₁ - w₁) + (W.γ T w₂ - w₂) := by
    rw [map_add]; abel
  rw [← e] at hS
  refine ⟨κ₁ + κ₂, κ₁' + κ₂', _, hS, ?_⟩
  have := inMultiple_add W T c j _ (inMultiple_lA_pow_smul W T c j _ (κ₂' + κ₂) hX₁) (inMultiple_lA_pow_smul W T c j _ (κ₁' + κ₁) hX₂)
  convert this using 1
  rw [map_add, φpow_lsmul, φpow_lsmul]
  exact lin_gadd _ _ _ _ _ _ _ _ _ _

theorem good_cong (T : LocLat G Qp LL O) (hC : Ctx W T) (c : ZMod n) (j y M σ : ℕ)
    (hM : y ≤ (PD.p - 1) * M) {w τ τ' : W.DD T}
    (h : Good W T c j y M σ w τ) (h' : Good W T c j y M σ w τ') :
    ∃ N, Formalism.MainNotions.ArcLiftingSetup.InFP W T c j (Formalism.MainNotions.LiftingTheory.JJ W j y M) (Formalism.MainNotions.ArcLiftingSetup.lA W ^ N • (τ - τ')) := by
  obtain ⟨κ₁, κ₁', S₁, hS₁, hX₁⟩ := h
  obtain ⟨κ₂, κ₂', S₂, hS₂, hX₂⟩ := h'
  have a₁ := solOK_scale W T c M κ₂ hS₁
  have a₂ := solOK_scale W T c M κ₁ hS₂
  rw [add_comm κ₂ κ₁] at a₂
  obtain ⟨K, hK⟩ := solOK_cong W T hC c j y M hM a₁ a₂
  refine ⟨K + κ₁' + κ₂' + κ₁ + κ₂, ?_⟩
  have := inMultiple_sub W T c j _
    (inMultiple_add W T c j _ (inMultiple_lA_pow_smul W T c j _ (K + κ₂' + κ₂) hX₁)
      (inMultiple_lA_pow_smul W T c j _ (κ₁' + κ₂' + σ) hK))
    (inMultiple_lA_pow_smul W T c j _ (K + κ₁' + κ₁) hX₂)
  convert this using 1
  rw [φpow_lsmul, φpow_lsmul]
  exact lin_gcong _ _ _ _ _ _ _ _ _ _ _

theorem good_map {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) (hT : IsCrys PD T.ρ)
    (hT' : IsCrys PD T'.ρ) (c : ZMod n) (j y M σ : ℕ)
    {w τ : W.DD T} (h : Good W T c j y M σ w τ) : Good W T' c j y M σ (W.map f w) (W.map f τ) := by
  obtain ⟨κ, κ', S, hS, hX⟩ := h
  have hS' := solOK_map W f hT hT' c M hS
  rw [map_sub] at hS'
  refine ⟨κ, κ', W.map f S, ?_, ?_⟩
  · convert hS' using 2
    exact (W.map_γ f W.gam w).symm
  · have := inMultiple_map W f hT hT' c j _ hX
    convert this using 1
    rw [mapA_smul, map_sub, mapA_smul, mapA_smul, map_φpow]

theorem good_self (T : LocLat G Qp LL O) (c : ZMod n) (j y M σ : ℕ) {w : W.DD T}
    (hw : ∃ w', Formalism.MainNotions.LiftingTheory.InNΔi W T c w' ∧ w = W.π₀ • w') :
    Good W T c j y M σ w (Formalism.MainNotions.ArcLiftingSetup.lA W ^ σ • ((W.φD T) ^ j) w) := by
  refine ⟨0, 0, w, ⟨hw, 0, InNΔi_zero W T c, by simp⟩, ?_⟩
  simpa using inMultiple_zero W T c j _

theorem good_to (T : LocLat G Qp LL O) (hC : Ctx W T) (c : ZMod n) (j y M σ : ℕ)
    (hM : y ≤ (PD.p - 1) * M) {w τ S₂ : W.DD T} {κ₂ : ℕ}
    (h : Good W T c j y M σ w τ) (hS₂ : SolOK W T c M (W.γ T w - w) κ₂ S₂) :
    ∃ κ', Formalism.MainNotions.ArcLiftingSetup.InFP W T c j (Formalism.MainNotions.LiftingTheory.JJ W j y M)
      (Formalism.MainNotions.ArcLiftingSetup.lA W ^ κ' • (Formalism.MainNotions.ArcLiftingSetup.lA W ^ κ₂ • τ -
        Formalism.MainNotions.ArcLiftingSetup.lA W ^ σ • ((W.φD T) ^ j) S₂)) := by
  obtain ⟨κ₁, κ₁', S₁, hS₁, hX₁⟩ := h
  have a₁ := solOK_scale W T c M κ₂ hS₁
  have a₂ := solOK_scale W T c M κ₁ hS₂
  rw [add_comm κ₂ κ₁] at a₂
  obtain ⟨K, hK⟩ := solOK_cong W T hC c j y M hM a₁ a₂
  refine ⟨K + κ₁' + κ₁, ?_⟩
  have := inMultiple_add W T c j _ (inMultiple_lA_pow_smul W T c j _ (K + κ₂) hX₁) (inMultiple_lA_pow_smul W T c j _ (κ₁' + σ) hK)
  convert this using 1
  rw [φpow_lsmul, φpow_lsmul]
  exact lin_gto _ _ _ _ _ _ _ _ _

end Formalism.MainNotions.UnusedSlot80.Relay2

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.Relay2

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem arith_M (p G h : ℕ) (hp : 2 ≤ p) (hG : G ≤ h) : 2 * G ≤ (p - 1) * (2 * h / (p - 1) + 1) := by
  have h1 := Nat.div_add_mod (2 * h) (p - 1)
  have h2 := Nat.mod_lt (2 * h) (show p - 1 > 0 by omega)
  rw [Nat.mul_add, Nat.mul_one]
  omega

theorem M_pos {n : ℕ} (A : Formalism.MainNotions.ArcLiftingSetup.ArcP n) (l : ℕ) : 1 ≤ A.M l := by
  unfold Formalism.MainNotions.ArcLiftingSetup.ArcP.M; exact Nat.le_add_left 1 _

def Ex (l r : ℕ) : ℕ := ⌈(r : ℝ) * l / ((l : ℝ) - 1)⌉₊

theorem Ex_mono (l : ℕ) (hl : 2 ≤ l) {r s : ℕ} (h : r ≤ s) : Ex l r ≤ Ex l s := by
  unfold Ex
  apply Nat.ceil_mono
  have : (0 : ℝ) < (l : ℝ) - 1 := by
    have : (2 : ℝ) ≤ l := by exact_mod_cast hl
    linarith
  apply div_le_div_of_nonneg_right _ this.le
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact_mod_cast h

theorem int_of_bd (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x) (r : ℕ)
    (h4 : ((r + padicValNat PD.p r.factorial : ℕ) : ℚ) ≤ r * PD.p / ((PD.p : ℚ) - 1))
    (x : LL) (hx : Formalism.MainNotions.LiftingTheory.Bd W r x) :
    ∃ o : O, algebraMap O LL o = (PD.p : LL) ^ Ex PD.p r * x := by
  apply hO2
  have hE := Formalism.MainNotions.LiftingTheory.tr_ceil_ge PD.p r
  rw [v.map_mul, v.map_pow, W.v_l, nsmul_one]
  unfold Formalism.MainNotions.LiftingTheory.Bd at hx
  induction hvx : v x using WithTop.recTopCoe with
  | top => simp
  | coe q =>
    rw [hvx] at hx
    rw [← WithTop.coe_natCast, ← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_le_coe]
    have hq : -(((r + padicValNat PD.p r.factorial : ℕ) : ℚ)) ≤ q := by exact_mod_cast hx
    unfold Ex at *
    linarith

theorem solOK_of_sol (T : LocLat G Qp LL O) (hinj : Function.Injective (algebraMap O LL))
    (hπ : W.π₀ ∈ W.AΔ) (c : ZMod n) {d : ℕ} (b : Fin d → W.DD T) (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T c b)
    (Z : W.DD T) (cf : ℕ → Fin d → LL) (hsol : Formalism.MainNotions.LiftingTheory.IsSol W T c b Z cf) (hc0 : cf 0 = 0)
    (M : ℕ) (hM : 1 ≤ M) (κ : ℕ) (y : ℕ → Fin d → O)
    (hy : ∀ r < M, ∀ m, algebraMap O LL (y r m) = (PD.p : LL) ^ κ * cf r m) :
    SolOK W T c M Z κ (∑ r ∈ Finset.range M, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b (y r)) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
    have hy0 : y 0 = 0 := by
      funext m
      apply hinj
      rw [hy 0 (by omega) m, hc0]
      simp
    refine ⟨∑ r ∈ Finset.range M', W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b (y (r + 1)),
      InNΔi_sum W T c _ _ fun r _ => InNΔi_smul W T c (W.AΔ.pow_mem hπ _)
        (Formalism.MainNotions.LiftingTheory.frame_vecB_mem W T c b hb _), ?_⟩
    rw [Finset.sum_range_succ', hy0, Finset.smul_sum]
    have h0 : Formalism.MainNotions.LiftingTheory.vecB W T b 0 = 0 := by simp [Formalism.MainNotions.LiftingTheory.vecB]
    rw [h0, smul_zero, add_zero]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [smul_smul, pow_succ']
  · obtain ⟨x, hx, hx'⟩ := hsol M κ y hy
    exact ⟨x, hx, by rw [← lsmul_eq]; exact hx'⟩

theorem solData (T : LocLat G Qp LL O) (c : ZMod n) (hm : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀)
    (h3 : ∀ (d : ℕ) (b : Fin d → W.DD T), Formalism.MainNotions.LiftingTheory.IsFrameΔ W T c b →
      ∀ z : W.DD T, (∃ z', Formalism.MainNotions.LiftingTheory.InNΔi W T c z' ∧ z = W.π₀ • z') → ∀ c₀ : Fin d → O,
        (∃ cf : ℕ → Fin d → LL, Formalism.MainNotions.LiftingTheory.IsSol W T c b z cf ∧ cf 0 = fun m => algebraMap O LL (c₀ m)) ∧
        ∀ cf : ℕ → Fin d → LL, Formalism.MainNotions.LiftingTheory.IsSol W T c b z cf → cf 0 = (fun m => algebraMap O LL (c₀ m)) →
          ∀ r m, Formalism.MainNotions.LiftingTheory.Bd W r (cf r m))
    (Z : W.DD T) (hZ : ∃ z', Formalism.MainNotions.LiftingTheory.InNΔi W T c z' ∧ Z = W.π₀ • z') :
    ∃ (d : ℕ) (b : Fin d → W.DD T) (cf : ℕ → Fin d → LL), Formalism.MainNotions.LiftingTheory.IsFrameΔ W T c b ∧
      Formalism.MainNotions.LiftingTheory.IsSol W T c b Z cf ∧ cf 0 = 0 ∧ ∀ r m, Formalism.MainNotions.LiftingTheory.Bd W r (cf r m) := by
  obtain ⟨d, b, hb⟩ := frame_exists W T c hm
  obtain ⟨⟨cf, hcf, hc0⟩, hbd⟩ := h3 d b hb Z hZ 0
  have hc0' : cf 0 = 0 := by rw [hc0]; funext m; simp
  exact ⟨d, b, cf, hb, hcf, hc0', hbd cf hcf hc0⟩

theorem intCoeffs (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x) (hl : 2 ≤ PD.p)
    (h4 : ∀ r : ℕ, ((r + padicValNat PD.p r.factorial : ℕ) : ℚ) ≤ r * PD.p / ((PD.p : ℚ) - 1))
    {d : ℕ} (cf : ℕ → Fin d → LL) (hbd : ∀ r m, Formalism.MainNotions.LiftingTheory.Bd W r (cf r m)) (M : ℕ) :
    ∃ y : ℕ → Fin d → O, ∀ r < M, ∀ m,
      algebraMap O LL (y r m) = (PD.p : LL) ^ Ex PD.p M * cf r m := by
  have hg : ∀ r m, ∃ o : O, algebraMap O LL o = (PD.p : LL) ^ Ex PD.p r * cf r m :=
    fun r m => int_of_bd W hO2 r (h4 r) _ (hbd r m)
  choose g hg using hg
  refine ⟨fun r m => ((PD.p : ℕ) : O) ^ (Ex PD.p M - Ex PD.p r) * g r m, fun r hr m => ?_⟩
  have hle := Ex_mono PD.p hl hr.le
  simp only [map_mul, map_pow, map_natCast, hg]
  rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]

theorem isTr_of (T : LocLat G Qp LL O) (hC : Ctx W T) (A : Formalism.MainNotions.ArcLiftingSetup.ArcP n) (c : ZMod n)
    (hM : 2 * A.G₀ ≤ (PD.p - 1) * A.M PD.p) {w τ : W.DD T}
    (hτ : Formalism.MainNotions.ArcLiftingSetup.InFP W T c A.j W.π₀ τ)
    (hG : Good W T c A.j (2 * A.G₀) (A.M PD.p) (A.σ PD.p) w τ)
    {d : ℕ} (b : Fin d → W.DD T) (cf : ℕ → Fin d → LL) (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T c b)
    (hsol : Formalism.MainNotions.LiftingTheory.IsSol W T c b (W.γ T w - w) cf) (hc0 : cf 0 = 0) (κ : ℕ)
    (y : ℕ → Fin d → O) (hy : ∀ r < A.M PD.p, ∀ m, algebraMap O LL (y r m) = (PD.p : LL) ^ κ * cf r m) :
    Formalism.MainNotions.ArcLiftingSetup.IsTr W A T c w τ := by
  have hS := solOK_of_sol W T hC.inj hC.hπ c b hb _ cf hsol hc0 (A.M PD.p) (M_pos A _) κ y hy
  obtain ⟨κ', hκ'⟩ := good_to W T hC c A.j (2 * A.G₀) (A.M PD.p) (A.σ PD.p) hM hG hS
  exact ⟨hτ, d, b, cf, hb, hsol, hc0, κ, κ', y, hy, hκ'⟩

theorem good_of_isTr (T : LocLat G Qp LL O) (hinj : Function.Injective (algebraMap O LL))
    (hπ : W.π₀ ∈ W.AΔ) (A : Formalism.MainNotions.ArcLiftingSetup.ArcP n) (c : ZMod n) {w τ : W.DD T}
    (h : Formalism.MainNotions.ArcLiftingSetup.IsTr W A T c w τ) :
    Formalism.MainNotions.ArcLiftingSetup.InFP W T c A.j W.π₀ τ ∧ Good W T c A.j (2 * A.G₀) (A.M PD.p) (A.σ PD.p) w τ := by
  obtain ⟨hτ, d, b, cf, hb, hsol, hc0, κ, κ', y, hy, hJ⟩ := h
  exact ⟨hτ, κ, κ', _, solOK_of_sol W T hinj hπ c b hb _ cf hsol hc0 (A.M PD.p) (M_pos A _) κ y hy, hJ⟩

end Formalism.MainNotions.UnusedSlot80.Relay2

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.Relay2

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem piPow_dvd (hO : ∀ c : O, ((PD.p : ℕ) : O) * c = 0 → c = 0) {e m : ℕ} {a c : LetA O n}
    (h : ((PD.p : ℕ) : LetA O n) ^ e * a = letπ ^ m * c) : ∃ a' : LetA O n, a = letπ ^ m * a' := by
  have hpow : ∀ (k : ℕ) (x : O), ((PD.p : ℕ) : O) ^ k * x = 0 → x = 0 := by
    intro k; induction k with
    | zero => intro x hx; simpa using hx
    | succ k ih => intro x hx; exact ih x (hO _ (by rw [← hx]; ring))
  have hi : ∀ i, ∃ q : PowerSeries O, a i = PowerSeries.X ^ m * q := by
    intro i
    refine (PowerSeries.X_pow_dvd_iff.2 fun k hk => ?_)
    have h1 := congrArg (fun z : LetA O n => PowerSeries.coeff k (z i)) h
    simp only [Pi.mul_apply, Pi.pow_apply, Pi.natCast_apply, letπ] at h1
    rw [← map_natCast (PowerSeries.C (R := O)), ← map_pow, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_X_pow_mul', if_neg (by omega)] at h1
    exact hpow e _ h1
  choose q hq using hi
  exact ⟨q, funext fun i => by simp [hq i, letπ]⟩

theorem frobenius_uniformizer_pow_dvd [IsDomain O] (h9 : Formalism.MainNotions.LiftingTheory.UniformizerRingClause W) (hO : ∀ c : O, ((PD.p : ℕ) : O) * c = 0 → c = 0)
    (Tr2 : ∀ j r : ℕ, ∃ u ∈ W.AΔ, ∃ u' ∈ W.AΔ, u * u' = 1 ∧
      ((W.φA ^ j) W.π₀) ^ r = u * W.π₀ ^ r * ∏ k ∈ Finset.range j, Formalism.MainNotions.LiftingTheory.pk W k ^ ((PD.p - 1) * r))
    (j y M r s E : ℕ) (hr : 1 ≤ r) (hM : 1 ≤ M) {a B : LetA O n} (ha : a ∈ W.AΔ)
    (h : ((PD.p : ℕ) : LetA O n) ^ s * ((W.φA ^ j) W.π₀) ^ r =
      a * ((PD.p : ℕ) : LetA O n) ^ E + B * Formalism.MainNotions.LiftingTheory.JJ W j y M) :
    ∃ a'' ∈ W.AΔ, a = W.π₀ * a'' := by
  obtain ⟨u, -, -, -, -, hu⟩ := Tr2 j r
  obtain ⟨w, hw⟩ := h9.2.2.1
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
  set X : LetA O n := ((PD.p : ℕ) : LetA O n) ^ s * (u * W.π₀ ^ r' *
      ∏ k ∈ Finset.range j, Formalism.MainNotions.LiftingTheory.pk W k ^ ((PD.p - 1) * (r' + 1))) -
      B * (W.π₀ ^ M' * ∏ k ∈ Finset.range j, Formalism.MainNotions.LiftingTheory.pk W k ^ y) with hX
  have e1 : ((PD.p : ℕ) : LetA O n) ^ E * a = letπ ^ (PD.p - 1) * ((w : LetA O n) * X) := by
    have : a * ((PD.p : ℕ) : LetA O n) ^ E = W.π₀ * X := by
      rw [hX, eq_sub_iff_add_eq.2 h.symm, hu, Formalism.MainNotions.LiftingTheory.JJ]
      ring
    rw [mul_comm, this, hw]; ring
  obtain ⟨a', ha'⟩ := piPow_dvd hO e1
  refine ⟨((w⁻¹ : (LetA O n)ˣ) : LetA O n) * a', ?_, ?_⟩
  · refine Formalism.MainNotions.LiftingTheory.tr_quot_mem W h9.1 (Formalism.MainNotions.LiftingTheory.tr_π₀_ne W h9) ha ?_
    rw [ha', hw]
    have : (w : LetA O n) * ((w⁻¹ : (LetA O n)ˣ) : LetA O n) = 1 := Units.mul_inv w
    linear_combination (-(letπ ^ (PD.p - 1) * a')) * this
  · rw [ha', hw]
    have : (w : LetA O n) * ((w⁻¹ : (LetA O n)ˣ) : LetA O n) = 1 := Units.mul_inv w
    linear_combination (-(letπ ^ (PD.p - 1) * a')) * this

theorem termId {R : Type} [CommRing R] (L π Φ G a B J : R) (s1 s k1 E K S : ℕ) (hK : K = k1 + E)
    (hS : S = s1 + s) (H : L ^ s * Φ * G = (π * a * L ^ E + B * J) * G) :
    L ^ K * (π * (L ^ s1 * G * a)) - L ^ S * (Φ * (L ^ k1 * G)) = J * (-(L ^ s1 * L ^ k1 * G * B)) := by
  subst hK hS
  linear_combination (-(L ^ s1 * L ^ k1)) * H

theorem sig_le {n : ℕ} (A : Formalism.MainNotions.ArcLiftingSetup.ArcP n) (l : ℕ) :
    Formalism.NOK.sigNOK l (2 * A.G₀) (A.M l) A.j ≤ A.σ l := by
  unfold Formalism.NOK.sigNOK Formalism.MainNotions.ArcLiftingSetup.ArcP.σ
  set x : ℝ := (((2 * A.G₀ : ℕ) : ℝ) + (A.M l : ℝ) / (l : ℝ) ^ (A.j - 1)) * l / ((l : ℝ) - 1) ^ 2
  have hx : 0 ≤ x := by positivity
  have h1 := Nat.floor_le hx
  have h2 := Nat.le_ceil (x + 1)
  have : ((⌊x⌋₊ + 1 : ℕ) : ℝ) ≤ (⌈x + 1⌉₊ : ℝ) := by push_cast; linarith
  exact_mod_cast this

end Formalism.MainNotions.UnusedSlot80.Relay2

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.Relay2

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem tau_exists [IsDomain O] (T : LocLat G Qp LL O) (hC : Ctx W T) (h9 : Formalism.MainNotions.LiftingTheory.UniformizerRingClause W)
    (hp2 : PD.p ≠ 2) (A : Formalism.MainNotions.ArcLiftingSetup.ArcP n) (hj : 1 ≤ A.j)
    (hM : 2 * A.G₀ ≤ (PD.p - 1) * A.M PD.p) (c : ZMod n) (w : W.DD T)
    {d : ℕ} (b : Fin d → W.DD T) (cf : ℕ → Fin d → LL) (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T c b)
    (hsol : Formalism.MainNotions.LiftingTheory.IsSol W T c b (W.γ T w - w) cf) (hc0 : cf 0 = 0)
    (hbd : ∀ r m, Formalism.MainNotions.LiftingTheory.Bd W r (cf r m))
    (h4 : ∀ r : ℕ, ((r + padicValNat PD.p r.factorial : ℕ) : ℚ) ≤ r * PD.p / ((PD.p : ℚ) - 1)) :
    ∃ τ, Formalism.MainNotions.ArcLiftingSetup.IsTr W A T c w τ := by
  have hl : 2 ≤ PD.p := PD.hp.two_le
  have hO := SatW.p_nzd_O W hC.inj
  have hg : ∀ r m, ∃ o : O, algebraMap O LL o = (PD.p : LL) ^ Ex PD.p r * cf r m :=
    fun r m => int_of_bd W hC.O2 r (h4 r) _ (hbd r m)
  choose g hg using hg
  have hg0 : ∀ m, g 0 m = 0 := fun m => hC.inj (by rw [hg, hc0]; simp)
  have hdec : ∀ r, ∃ a'' ∈ W.AΔ, ∃ B ∈ W.AΔ, ∀ m,
      ((PD.p : ℕ) : LetA O n) ^ Formalism.NOK.sigNOK PD.p (2 * A.G₀) (A.M PD.p) A.j *
          ((W.φA ^ A.j) W.π₀) ^ r * algebraMap O (LetA O n) (g r m) =
        (W.π₀ * a'' * ((PD.p : ℕ) : LetA O n) ^ Ex PD.p r +
          B * Formalism.MainNotions.LiftingTheory.JJ W A.j (2 * A.G₀) (A.M PD.p)) * algebraMap O (LetA O n) (g r m) := by
    intro r
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · exact ⟨0, W.AΔ.zero_mem, 0, W.AΔ.zero_mem, fun m => by simp [hg0]⟩
    · obtain ⟨a, ha, B, hB, h⟩ := Formalism.MainNotions.LiftingTheory.tr_trunc_int W h9 hp2 A.j (2 * A.G₀) (A.M PD.p) r hj
      obtain ⟨a'', ha'', rfl⟩ := frobenius_uniformizer_pow_dvd W h9 hO hC.Tr2 A.j (2 * A.G₀) (A.M PD.p) r _ _ hr
        (M_pos A _) ha h
      exact ⟨a'', ha'', B, hB, fun m => by rw [h]; rfl⟩
  choose a'' ha'' B hB heq using hdec
  set M := A.M PD.p with hMdef
  set κ := Ex PD.p M with hκ
  set σ := A.σ PD.p with hσ
  set sg := Formalism.NOK.sigNOK PD.p (2 * A.G₀) M A.j with hsg
  have hsgσ : sg ≤ σ := sig_le A PD.p
  let y : ℕ → Fin d → O := fun r m => ((PD.p : ℕ) : O) ^ (κ - Ex PD.p r) * g r m
  have hy : ∀ r < M, ∀ m, algebraMap O LL (y r m) = (PD.p : LL) ^ κ * cf r m := by
    intro r hr m
    have hle := Ex_mono PD.p hl hr.le
    simp only [y, map_mul, map_pow, map_natCast, hg]
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
  have hyA : ∀ r m, algebraMap O (LetA O n) (y r m) =
      Formalism.MainNotions.ArcLiftingSetup.lA W ^ (κ - Ex PD.p r) * algebraMap O (LetA O n) (g r m) := by
    intro r m; simp only [y, map_mul, map_pow, map_natCast]; rfl
  let β : Fin d → W.DD T := fun m => ((W.φD T) ^ A.j) (b m)
  have hβ : ∀ m, β m ∈ Formalism.MainNotions.ArcLiftingSetup.Pp W T c A.j := fun m => Pp_phi W T c A.j (hb.1 m)
  have hcoefΔ : ∀ r m, Formalism.MainNotions.ArcLiftingSetup.lA W ^ (σ - sg) * algebraMap O (LetA O n) (g r m) * a'' r ∈ W.AΔ :=
    fun r m => W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.pow_mem (lA_mem W) _) (W.AΔ.algebraMap_mem _)) (ha'' r)
  let τ : W.DD T := W.π₀ • ∑ r ∈ Finset.range M, ∑ m,
    (Formalism.MainNotions.ArcLiftingSetup.lA W ^ (σ - sg) * algebraMap O (LetA O n) (g r m) * a'' r) • β m
  have hτ : Formalism.MainNotions.ArcLiftingSetup.InFP W T c A.j W.π₀ τ :=
    ⟨_, AddSubgroup.sum_mem _ fun r _ => AddSubgroup.sum_mem _ fun m _ =>
      Pp_smul W T c A.j (hcoefΔ r m) _ (hβ m), rfl⟩
  have hS := solOK_of_sol W T hC.inj hC.hπ c b hb _ cf hsol hc0 M (M_pos A _) κ y hy
  set S := ∑ r ∈ Finset.range M, W.π₀ ^ r • Formalism.MainNotions.LiftingTheory.vecB W T b (y r) with hSdef
  have hφS : ((W.φD T) ^ A.j) S = ∑ r ∈ Finset.range M, ∑ m,
      (((W.φA ^ A.j) W.π₀) ^ r * algebraMap O (LetA O n) (y r m)) • β m := by
    rw [hSdef, map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [φpow_smul, map_pow, Formalism.MainNotions.LiftingTheory.vecB, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_smul, ← algebraMap_smul (LetA O n) (y r m), smul_smul]
  have key : Formalism.MainNotions.ArcLiftingSetup.lA W ^ 0 • (Formalism.MainNotions.ArcLiftingSetup.lA W ^ κ • τ - Formalism.MainNotions.ArcLiftingSetup.lA W ^ σ • ((W.φD T) ^ A.j) S) =
      Formalism.MainNotions.LiftingTheory.JJ W A.j (2 * A.G₀) M • ∑ r ∈ Finset.range M, ∑ m,
        (-(Formalism.MainNotions.ArcLiftingSetup.lA W ^ (σ - sg) * Formalism.MainNotions.ArcLiftingSetup.lA W ^ (κ - Ex PD.p r) *
          algebraMap O (LetA O n) (g r m) * B r)) • β m := by
    rw [hφS, pow_zero, one_smul, smul_smul, Finset.smul_sum, Finset.smul_sum, Finset.smul_sum,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r hr => ?_
    rw [Finset.smul_sum, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_smul, smul_smul, ← sub_smul, smul_smul]
    congr 1
    have hle := Ex_mono PD.p hl (Finset.mem_range.1 hr).le
    have := termId (Formalism.MainNotions.ArcLiftingSetup.lA W) W.π₀ (((W.φA ^ A.j) W.π₀) ^ r)
      (algebraMap O (LetA O n) (g r m)) (a'' r) (B r) (Formalism.MainNotions.LiftingTheory.JJ W A.j (2 * A.G₀) M)
      (σ - sg) sg (κ - Ex PD.p r) (Ex PD.p r) κ σ (by omega) (by omega) (heq r m)
    rw [hyA]
    linear_combination this
  have hGood : Good W T c A.j (2 * A.G₀) M σ w τ := by
    refine ⟨κ, 0, S, hS, ?_⟩
    rw [key]
    refine inMultiple_of_mem W T c A.j _ (AddSubgroup.sum_mem _ fun r _ => AddSubgroup.sum_mem _ fun m _ =>
      Pp_smul W T c A.j ?_ _ (hβ m))
    exact W.AΔ.neg_mem (W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.pow_mem (lA_mem W) _)
      (W.AΔ.pow_mem (lA_mem W) _)) (W.AΔ.algebraMap_mem _)) (hB r))
  exact ⟨τ, isTr_of W T hC A c hM hτ hGood b cf hb hsol hc0 κ y hy⟩

end Formalism.MainNotions.UnusedSlot80.Relay2

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.Relay2

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem InFNc_zero (T : LocLat G Qp LL O) (c : ZMod n) (f : LetA O n) : Formalism.MainNotions.ArcLiftingSetup.InFNc W T c f 0 :=
  ⟨0, (W.NΔ T).zero_mem, smul_zero _, (smul_zero _).symm⟩

theorem InFNc_add (T : LocLat G Qp LL O) (c : ZMod n) (f : LetA O n) {x y : W.DD T}
    (hx : Formalism.MainNotions.ArcLiftingSetup.InFNc W T c f x) (hy : Formalism.MainNotions.ArcLiftingSetup.InFNc W T c f y) :
    Formalism.MainNotions.ArcLiftingSetup.InFNc W T c f (x + y) := by
  obtain ⟨a, ha, hac, rfl⟩ := hx
  obtain ⟨b, hb, hbc, rfl⟩ := hy
  exact ⟨a + b, (W.NΔ T).add_mem ha hb, by rw [smul_add, hac, hbc], (smul_add _ _ _).symm⟩

theorem InFNc_neg (T : LocLat G Qp LL O) (c : ZMod n) (f : LetA O n) {x : W.DD T}
    (hx : Formalism.MainNotions.ArcLiftingSetup.InFNc W T c f x) : Formalism.MainNotions.ArcLiftingSetup.InFNc W T c f (-x) := by
  obtain ⟨a, ha, hac, rfl⟩ := hx
  exact ⟨-a, (W.NΔ T).neg_mem ha, by rw [smul_neg, hac], (smul_neg _ _).symm⟩

theorem InFNc_sub (T : LocLat G Qp LL O) (c : ZMod n) (f : LetA O n) {x y : W.DD T}
    (hx : Formalism.MainNotions.ArcLiftingSetup.InFNc W T c f x) (hy : Formalism.MainNotions.ArcLiftingSetup.InFNc W T c f y) :
    Formalism.MainNotions.ArcLiftingSetup.InFNc W T c f (x - y) := by
  rw [sub_eq_add_neg]; exact InFNc_add W T c f hx (InFNc_neg W T c f hy)

theorem InFNc_smul (T : LocLat G Qp LL O) (c : ZMod n) (f : LetA O n) {a : LetA O n} (ha : a ∈ W.AΔ)
    {x : W.DD T} (hx : Formalism.MainNotions.ArcLiftingSetup.InFNc W T c f x) : Formalism.MainNotions.ArcLiftingSetup.InFNc W T c f (a • x) := by
  obtain ⟨y, hy, hyc, rfl⟩ := hx
  exact ⟨a • y, SatW.smul_mem_NΔ W T ha hy, by rw [smul_comm, hyc], smul_comm _ _ _⟩

theorem InFNc_of_FP (T : LocLat G Qp LL O) (A : Formalism.MainNotions.ArcLiftingSetup.ArcP n) (c : ZMod n)
    (hfirst : ∀ y ∈ Formalism.MainNotions.ArcLiftingSetup.Pp W T c A.j,
      Formalism.MainNotions.ArcLiftingSetup.InFNc W T (c + (A.j : ZMod n)) (W.π₀ ^ A.M PD.p)
        (Formalism.MainNotions.LiftingTheory.JJ W A.j (2 * A.G₀) (A.M PD.p) • y) ∧
      Formalism.MainNotions.ArcLiftingSetup.InFNc W T (c + (A.j : ZMod n)) 1 ((∏ s ∈ Finset.range A.j, Formalism.MainNotions.ArcLiftingSetup.ps W s ^ A.G₀) • y))
    {x : W.DD T} (hx : Formalism.MainNotions.ArcLiftingSetup.InFP W T c A.j (Formalism.MainNotions.LiftingTheory.JJ W A.j (2 * A.G₀) (A.M PD.p)) x) :
    Formalism.MainNotions.ArcLiftingSetup.InFNc W T (c + (A.j : ZMod n)) (W.π₀ ^ A.M PD.p) x := by
  obtain ⟨z, hz, rfl⟩ := hx
  exact (hfirst z hz).1

theorem InFNc_γ (T : LocLat G Qp LL O) (hC : Ctx W T) (i : ZMod n) (r : ℕ) {x : W.DD T}
    (hx : Formalism.MainNotions.ArcLiftingSetup.InFNc W T i (W.π₀ ^ r) x) :
    Formalism.MainNotions.ArcLiftingSetup.InFNc W T i (W.π₀ ^ r) (W.γ T x - x) := by
  obtain ⟨y, hy, hyc, rfl⟩ := hx
  obtain ⟨y', hy', e⟩ := hC.H1 i r y (InNΔi_of W T i hy hyc)
  have hz : Formalism.MainNotions.LiftingTheory.InNΔi W T i ((Formalism.MainNotions.LiftingTheory.u₁ W ^ r - 1) • y + W.π₀ • y') :=
    InNΔi_add W T i (InNΔi_osmul W T i _ (InNΔi_of W T i hy hyc)) (InNΔi_smul W T i hC.hπ hy')
  refine ⟨_, hz.1, InNΔi_letter W T i hz, ?_⟩
  rw [e, smul_add, smul_smul, ← pow_succ, smul_comm]

theorem lin_gam {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (L : A) (κ κ' σ : ℕ)
    (P Q t₁ t₀ s₁ s₀ q : M) (e : s₁ - s₀ - L ^ κ • (P - Q) = q) :
    L ^ (κ' + κ) • (L ^ σ • P - t₁ - (L ^ σ • Q - t₀)) =
      -(L ^ κ' • (L ^ κ • t₁ - L ^ σ • s₁) - L ^ κ' • (L ^ κ • t₀ - L ^ σ • s₀)) - L ^ (κ' + σ) • q := by
  rw [← e]; module

theorem gamma_clause (T : LocLat G Qp LL O) (hC : Ctx W T) (hSAT : Formalism.MainNotions.ArcLiftingSetup.SATcore W)
    (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (hT : IsCrys PD T.ρ) (A : Formalism.MainNotions.ArcLiftingSetup.ArcP n) (c : ZMod n)
    (hM : 2 * A.G₀ ≤ (PD.p - 1) * A.M PD.p)
    (hfirst : ∀ y ∈ Formalism.MainNotions.ArcLiftingSetup.Pp W T c A.j,
      Formalism.MainNotions.ArcLiftingSetup.InFNc W T (c + (A.j : ZMod n)) (W.π₀ ^ A.M PD.p)
        (Formalism.MainNotions.LiftingTheory.JJ W A.j (2 * A.G₀) (A.M PD.p) • y) ∧
      Formalism.MainNotions.ArcLiftingSetup.InFNc W T (c + (A.j : ZMod n)) 1 ((∏ s ∈ Finset.range A.j, Formalism.MainNotions.ArcLiftingSetup.ps W s ^ A.G₀) • y))
    {w τ : W.DD T} (hw : Formalism.MainNotions.ArcLiftingSetup.InI W T c w) (hτ : τ ∈ Formalism.MainNotions.ArcLiftingSetup.Pp W T c A.j)
    (hG : Good W T c A.j (2 * A.G₀) (A.M PD.p) (A.σ PD.p) w τ) :
    Formalism.MainNotions.ArcLiftingSetup.InFNc W T (c + (A.j : ZMod n)) (W.π₀ ^ A.M PD.p)
      (W.γ T (Formalism.MainNotions.ArcLiftingSetup.lA W ^ (A.σ PD.p) • ((W.φD T) ^ A.j) w - τ) -
        (Formalism.MainNotions.ArcLiftingSetup.lA W ^ (A.σ PD.p) • ((W.φD T) ^ A.j) w - τ)) := by
  obtain ⟨κ, κ', S, ⟨-, x, hx, eS⟩, hX⟩ := hG
  set M := A.M PD.p
  set σ := A.σ PD.p
  set j := A.j
  set c' := c + (j : ZMod n)
  set V := W.γ T (Formalism.MainNotions.ArcLiftingSetup.lA W ^ σ • ((W.φD T) ^ j) w - τ) -
    (Formalism.MainNotions.ArcLiftingSetup.lA W ^ σ • ((W.φD T) ^ j) w - τ) with hV

  obtain ⟨z, hz, hzc, hzw⟩ := hw.2.2
  have hVP : V ∈ Formalism.MainNotions.ArcLiftingSetup.Pp W T c j := by
    have e : V = Formalism.MainNotions.ArcLiftingSetup.lA W ^ σ • ((W.φD T) ^ j) (W.π₀ • z) - (W.γ T τ - τ) := by
      have g1 : W.γ T (((W.φD T) ^ j) w) = ((W.φD T) ^ j) (W.γ T w) := γ_φpow W T W.gam j w
      rw [hV, map_sub, γ_lsmul, ← hzw, map_sub, smul_sub, g1]; abel
    rw [e]
    refine (Formalism.MainNotions.ArcLiftingSetup.Pp W T c j).sub_mem (Pp_smul W T c j (W.AΔ.pow_mem (lA_mem W) _) _ ?_)
      ((Formalism.MainNotions.ArcLiftingSetup.Pp W T c j).sub_mem (Pp_γ W T c j τ hτ) hτ)
    rw [φpow_smul]
    exact Pp_gen W T c j (PhiPowers.φA_pow_mem_AΔ W hC.hπ j) (InNΔi_of W T c hz hzc)

  have hX' := InFNc_of_FP W T A c hfirst hX
  have hq := InFNc_of_FP W T A c hfirst (phij_pi0pow W T c hC.hπ hC.Tr2 j _ M hM hx)
  have e2 : Formalism.MainNotions.ArcLiftingSetup.lA W ^ (κ' + κ) • V =
      -(W.γ T (Formalism.MainNotions.ArcLiftingSetup.lA W ^ κ' • (Formalism.MainNotions.ArcLiftingSetup.lA W ^ κ • τ -
          Formalism.MainNotions.ArcLiftingSetup.lA W ^ σ • ((W.φD T) ^ j) S)) -
        Formalism.MainNotions.ArcLiftingSetup.lA W ^ κ' • (Formalism.MainNotions.ArcLiftingSetup.lA W ^ κ • τ - Formalism.MainNotions.ArcLiftingSetup.lA W ^ σ • ((W.φD T) ^ j) S)) -
      Formalism.MainNotions.ArcLiftingSetup.lA W ^ (κ' + σ) • ((W.φD T) ^ j) (W.π₀ ^ M • x) := by
    have eφ := congrArg ((W.φD T) ^ j) eS
    rw [map_sub, map_sub, φpow_lsmul, map_sub] at eφ
    simp only [hV, map_sub, γ_lsmul]
    have g1 : W.γ T (((W.φD T) ^ j) w) = ((W.φD T) ^ j) (W.γ T w) := γ_φpow W T W.gam j w
    have g2 : W.γ T (((W.φD T) ^ j) S) = ((W.φD T) ^ j) (W.γ T S) := γ_φpow W T W.gam j S
    rw [g1, g2]
    exact lin_gam _ _ _ _ _ _ _ _ _ _ _ eφ
  have hlV : Formalism.MainNotions.ArcLiftingSetup.InFNc W T c' (W.π₀ ^ M) (Formalism.MainNotions.ArcLiftingSetup.lA W ^ (κ' + κ) • V) := by
    rw [e2]
    exact InFNc_sub W T c' _ (InFNc_neg W T c' _ (InFNc_γ W T hC c' M hX'))
      (InFNc_smul W T c' _ (W.AΔ.pow_mem (lA_mem W) _) hq)

  have hPr : (∏ s ∈ Finset.range j, Formalism.MainNotions.ArcLiftingSetup.ps W s ^ A.G₀) ∈ Formalism.MainNotions.ArcLiftingSetup.PiPs W :=
    Submonoid.prod_mem _ fun s _ => Submonoid.pow_mem _
      (Submonoid.subset_closure (Set.mem_insert_of_mem _ (Set.mem_range_self s))) _
  have hπM : W.π₀ ^ M ∈ Formalism.MainNotions.ArcLiftingSetup.PiPs W :=
    Submonoid.pow_mem _ (Submonoid.subset_closure (Set.mem_insert _ _)) _
  obtain ⟨yv, hyv, hyvc⟩ := (hfirst V hVP).2
  have hfV : (∏ s ∈ Finset.range j, Formalism.MainNotions.ArcLiftingSetup.ps W s ^ A.G₀) • V ∈ W.NΔ T := by
    rw [hyvc.2, one_smul]; exact hyv
  obtain ⟨u, hu, hle⟩ := hlV
  obtain ⟨y, hy, hyV⟩ := hSAT hA T (W.π₀ ^ M) _ hT hπM hPr V hfV ⟨κ' + κ, u, hu, hle.2⟩
  refine ⟨y, hy, ?_, hyV⟩
  have hVc : (letE c' : LetA O n) • V = V := Pp_letter W T c j V hVP
  have h0 : (letE c' : LetA O n) • y - y = 0 :=
    Formalism.MainNotions.LiftingTheory.frame_π₀_inj W T hC.hw M _ (by rw [smul_sub, smul_comm, ← hyV, hVc, sub_self])
  exact sub_eq_zero.1 h0

end Formalism.MainNotions.UnusedSlot80.Relay2

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.Relay2

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem arith_h (p h : ℕ) (hp : 2 ≤ p) : h < (p - 1) * (2 * h / (p - 1) + 1) := by
  have h1 := Nat.div_add_mod (2 * h) (p - 1)
  have h2 := Nat.mod_lt (2 * h) (show p - 1 > 0 by omega)
  rw [Nat.mul_add, Nat.mul_one]
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · simp; omega
  · omega

theorem jumpsLe_of_win (A : Formalism.MainNotions.ArcLiftingSetup.ArcP n) (hA : A.OK) (T : LocLat G Qp LL O)
    (hT : Formalism.MainNotions.ArcLiftingSetup.Win W A T) : Formalism.MainNotions.ArcLiftingSetup.JumpsLe PD T A.h := by
  intro τ a ha
  obtain ⟨i, hi⟩ := W.emb_bij.2 (τ.comp (IsScalarTower.toAlgHom Qp K₀ K))
  have hw := hT.2 i τ hi.symm a ha
  have hok := hA.2.2.2.2.1 i
  have hGh := hA.2.2.2.2.2.1
  have hth := hA.2.2.2.2.2.2.2.1 i
  revert hw hok hth
  cases A.ty i with
  | thin =>
    intro hw _ _
    simp only [Formalism.MainNotions.LocalTheoryWindows.LT.win, Set.mem_Icc] at hw
    rw [abs_le]; constructor <;> omega
  | up b =>
    intro hw hok hth
    simp only [Formalism.MainNotions.LocalTheoryWindows.LT.win, Set.mem_union, Set.mem_Icc] at hw
    simp only [Formalism.MainNotions.LocalTheoryWindows.LT.ok] at hok
    simp only [Formalism.MainNotions.LocalTheoryWindows.LT.thick, Formalism.MainNotions.LocalTheoryWindows.LT.size, forall_const] at hth
    rw [abs_le]; constructor <;> omega
  | down b =>
    intro hw hok hth
    simp only [Formalism.MainNotions.LocalTheoryWindows.LT.win, Set.mem_union, Set.mem_Icc] at hw
    simp only [Formalism.MainNotions.LocalTheoryWindows.LT.ok] at hok
    simp only [Formalism.MainNotions.LocalTheoryWindows.LT.thick, Formalism.MainNotions.LocalTheoryWindows.LT.size, forall_const] at hth
    rw [abs_le]; constructor <;> omega

theorem cls_unique (T : LocLat G Qp LL O) (M : ℕ) (hq : Formalism.MainNotions.ArcLiftingSetup.qA W ∈ W.AΔ)
    (hc1 : ∀ x ∈ W.NΔ T, Formalism.MainNotions.ArcLiftingSetup.InFN W T (W.π₀ ^ M * Formalism.MainNotions.ArcLiftingSetup.qA W) (W.φD T (W.π₀ ^ M • x)))
    (hc2 : ∀ z, Formalism.MainNotions.ArcLiftingSetup.InFN W T (W.π₀ ^ M) z →
      ∃ x, Formalism.MainNotions.ArcLiftingSetup.InFN W T (W.π₀ ^ M) x ∧ W.φD T x - x = z ∧
        ∀ x', Formalism.MainNotions.ArcLiftingSetup.InFN W T (W.π₀ ^ M) x' → W.φD T x' - x' = z → x' = x)
    {y : W.DD T} {x₁ x₂ : LatticeCohomology T.L} (h₁ : Formalism.MainNotions.ArcLiftingSetup.Cls W T M y x₁)
    (h₂ : Formalism.MainNotions.ArcLiftingSetup.Cls W T M y x₂) : x₁ = x₂ := by
  obtain ⟨z₁, m₁, hz₁, rfl⟩ := h₁
  obtain ⟨z₂, m₂, hz₂, rfl⟩ := h₂
  have e : ∀ z, (y, z) ∈ Formalism.MainNotions.ArcLiftingSetup.CocΔ W T → W.φD T z - z = W.γD T W.gamK y - y := by
    intro z m
    have m' := LinearMap.mem_ker.1 m.1
    simp only [LinearMap.coprod_apply, LinearMap.sub_apply, LinearMap.neg_apply,
      LinearMap.id_apply] at m'
    rw [← sub_eq_zero, ← neg_eq_zero, ← m']
    abel
  have hz : Formalism.MainNotions.ArcLiftingSetup.InFN W T (W.π₀ ^ M) (W.φD T z₁ - z₁) := by
    obtain ⟨u, hu, rfl⟩ := hz₁
    obtain ⟨u', hu', e'⟩ := hc1 u hu
    refine ⟨Formalism.MainNotions.ArcLiftingSetup.qA W • u' - u, (W.NΔ T).sub_mem (SatW.smul_mem_NΔ W T hq hu') hu, ?_⟩
    rw [e', mul_smul, smul_sub]
  obtain ⟨x, -, -, huniq⟩ := hc2 _ hz
  have h1 := huniq z₁ hz₁ rfl
  have h2 := huniq z₂ hz₂ (by rw [e z₂ m₂, ← e z₁ m₁])
  have : z₁ = z₂ := h1.trans h2.symm
  subst this
  rfl

theorem Ps_le_AΔ (hπ : W.π₀ ∈ W.AΔ) {Λ : LetA O n} (h : Λ ∈ Formalism.MainNotions.ArcLiftingSetup.Ps W) : Λ ∈ W.AΔ := by
  refine Submonoid.closure_induction (fun z hz => ?_) W.AΔ.one_mem
    (fun _ _ _ _ ha hb => W.AΔ.mul_mem ha hb) h
  obtain ⟨s, rfl⟩ := hz
  exact PhiPowers.ps_mem_AΔ W hπ s

theorem φ_Ps (j : ℕ) {Λ : LetA O n} (h : Λ ∈ Formalism.MainNotions.ArcLiftingSetup.Ps W) : (W.φA ^ j) Λ ∈ Formalism.MainNotions.ArcLiftingSetup.Ps W := by
  induction h using Submonoid.closure_induction with
  | mem z hz =>
    obtain ⟨s, rfl⟩ := hz
    refine Submonoid.subset_closure ⟨j + s, ?_⟩
    simp only [Formalism.MainNotions.ArcLiftingSetup.ps, pow_add, AlgHom.mul_apply]
  | one => rw [map_one]; exact Submonoid.one_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact Submonoid.mul_mem _ hx hy

theorem prodPs_mem (j G₀ : ℕ) : (∏ s ∈ Finset.range j, Formalism.MainNotions.ArcLiftingSetup.ps W s ^ G₀) ∈ Formalism.MainNotions.ArcLiftingSetup.Ps W :=
  Submonoid.prod_mem _ fun s _ => Submonoid.pow_mem _ (Submonoid.subset_closure (Set.mem_range_self (f := Formalism.MainNotions.ArcLiftingSetup.ps W) s)) _

theorem y_letter (T : LocLat G Qp LL O) (c : ZMod n) (j σ : ℕ) {w τ : W.DD T}
    (hw : Formalism.MainNotions.ArcLiftingSetup.InLet W T c w) (hτ : τ ∈ Formalism.MainNotions.ArcLiftingSetup.Pp W T c j) :
    Formalism.MainNotions.ArcLiftingSetup.InLet W T (c + (j : ZMod n)) (Formalism.MainNotions.ArcLiftingSetup.lA W ^ σ • ((W.φD T) ^ j) w - τ) := by
  show (letE (c + (j : ZMod n)) : LetA O n) • _ = _
  rw [smul_sub, smul_comm, PhiPowers.φD_pow_letter W T c w hw j, Pp_letter W T c j τ hτ]

theorem y_Δ (T : LocLat G Qp LL O) (c : ZMod n) (j σ : ℕ) {w τ : W.DD T}
    (hw : Formalism.MainNotions.ArcLiftingSetup.IsΔ W T w) (hτ : τ ∈ Formalism.MainNotions.ArcLiftingSetup.Pp W T c j) :
    Formalism.MainNotions.ArcLiftingSetup.IsΔ W T (Formalism.MainNotions.ArcLiftingSetup.lA W ^ σ • ((W.φD T) ^ j) w - τ) := by
  intro δ hδ
  rw [map_sub, ← lsmul_eq, map_smul, PhiPowers.φD_pow_Δ W T hw j δ hδ, Pp_Δ W T c j τ hτ δ hδ]

end Formalism.MainNotions.UnusedSlot80.Relay2

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.Relay2

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem ctx_of (hinj : Function.Injective (algebraMap O LL))
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hH : Formalism.MainNotions.LiftingTheory.coreH W) (hTr : Formalism.MainNotions.LiftingTheory.coreTr W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W)
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) : Ctx W T :=
  have hr := (Formalism.MainNotions.LiftingTheory.frame_p9A W h9 hA T hT).1
  { inj := hinj, O2 := hO2, hπ := hr.1, hw := hr.2.2.1, H1 := fun i => (hH hA T hT i).1,
    H2 := (hH hA T hT 0).2.1, Tr2 := (hTr hA).2.1 }

theorem mkTr [IsDomain O] (hinj : Function.Injective (algebraMap O LL))
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hH : Formalism.MainNotions.LiftingTheory.coreH W) (hTr : Formalism.MainNotions.LiftingTheory.coreTr W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W)
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (A : Formalism.MainNotions.ArcLiftingSetup.ArcP n)
    (hM : 2 * A.G₀ ≤ (PD.p - 1) * A.M PD.p) (c : ZMod n) {w τ : W.DD T}
    (hZ : ∃ z', Formalism.MainNotions.LiftingTheory.InNΔi W T c z' ∧ W.γ T w - w = W.π₀ • z')
    (hτ : Formalism.MainNotions.ArcLiftingSetup.InFP W T c A.j W.π₀ τ)
    (hG : Good W T c A.j (2 * A.G₀) (A.M PD.p) (A.σ PD.p) w τ) : Formalism.MainNotions.ArcLiftingSetup.IsTr W A T c w τ := by
  have hC := ctx_of W hinj hO2 h9 hH hTr hA T hT
  have hl : 2 ≤ PD.p := PD.hp.two_le
  obtain ⟨d, b, cf, hb, hsol, hc0, hbd⟩ :=
    solData W T c (Formalism.MainNotions.LiftingTheory.frame_p9A W h9 hA T hT).2 (hH hA T hT c).2.2.1 _ hZ
  obtain ⟨y, hy⟩ := intCoeffs W hO2 hl (hH hA T hT c).2.2.2.1 cf hbd (A.M PD.p)
  exact isTr_of W T hC A c hM hτ hG b cf hb hsol hc0 _ y hy

theorem Z_of_InI (T : LocLat G Qp LL O) (c : ZMod n) {w : W.DD T} (hw : Formalism.MainNotions.ArcLiftingSetup.InI W T c w) :
    ∃ z', Formalism.MainNotions.LiftingTheory.InNΔi W T c z' ∧ W.γ T w - w = W.π₀ • z' := by
  obtain ⟨z, hz, hzc, hzw⟩ := hw.2.2
  exact ⟨z, InNΔi_of W T c hz hzc, hzw⟩

theorem relayCore_of [IsDomain O] (hinj : Function.Injective (algebraMap O LL))
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (hH : Formalism.MainNotions.LiftingTheory.coreH W) (hTr : Formalism.MainNotions.LiftingTheory.coreTr W)
    (hSAT : Formalism.MainNotions.ArcLiftingSetup.SATcore W) (hSP : Formalism.MainNotions.ArcLiftingSetup.SATPcore W) (hF1 : Formalism.MainNotions.ArcLiftingSetup.FirstWachFiltration W)
    (hF2 : Formalism.MainNotions.ArcLiftingSetup.SecondWachFiltration W) : Formalism.MainNotions.ArcLiftingSetup.RelayCore W := by
  intro hA hp5 A hAok c hc
  have hs : W.s = 1 := hA.2.1
  have hp2 : PD.p ≠ 2 := hA.2.2
  have hl : 2 ≤ PD.p := PD.hp.two_le
  have hj : 1 ≤ A.j := hAok.2.1
  have hM : 2 * A.G₀ ≤ (PD.p - 1) * A.M PD.p := arith_M PD.p A.G₀ A.h hl hAok.2.2.2.2.2.1
  have hlt : A.h < (PD.p - 1) * A.M PD.p := arith_h PD.p A.h hl
  have hF := hF1 hA A.h (A.M PD.p) hlt
  set j := A.j
  set M := A.M PD.p
  set σ := A.σ PD.p
  refine ⟨fun T hT => ?_, ?_⟩
  · have hTc : IsCrys PD T.ρ := hT.1
    have hJ := jumpsLe_of_win W A hAok T hT
    obtain ⟨hc1, hc2, hc3, hc4, hc5⟩ := hF.1 T hTc hJ
    have hring := (Formalism.MainNotions.LiftingTheory.frame_p9A W h9 hA T hTc).1
    have hC := ctx_of W hinj hO2 h9 hH hTr hA T hTc
    have hfirst := PhiPowers.relay_first W hs hring h5 A hAok c hc T hT
    have hq : Formalism.MainNotions.ArcLiftingSetup.qA W ∈ W.AΔ := W.AΔ.add_mem hC.hπ (W.AΔ.natCast_mem _)
    have hTP : ∀ {w τ}, Formalism.MainNotions.ArcLiftingSetup.IsTr W A T c w τ → τ ∈ Formalism.MainNotions.ArcLiftingSetup.Pp W T c j := fun h =>
      mem_Pp_of_inMultiple W T c j hC.hπ (good_of_isTr W T hinj hC.hπ A c h).1
    have exTau : ∀ w, Formalism.MainNotions.ArcLiftingSetup.InI W T c w → ∃ τ, Formalism.MainNotions.ArcLiftingSetup.IsTr W A T c w τ := by
      intro w hw
      obtain ⟨d, b, cf, hb, hsol, hc0, hbd⟩ :=
        solData W T c (Formalism.MainNotions.LiftingTheory.frame_p9A W h9 hA T hTc).2 (hH hA T hTc c).2.2.1 _ (Z_of_InI W T c hw)
      exact tau_exists W T hC hring hp2 A hj hM c w b cf hb hsol hc0 hbd (hH hA T hTc c).2.2.2.1
    have clB : ∀ w τ τ', Formalism.MainNotions.ArcLiftingSetup.IsTr W A T c w τ → Formalism.MainNotions.ArcLiftingSetup.IsTr W A T c w τ' →
        Formalism.MainNotions.ArcLiftingSetup.InFP W T c j (Formalism.MainNotions.LiftingTheory.JJ W j (2 * A.G₀) M) (τ - τ') := by
      intro w τ τ' h h'
      obtain ⟨N, hN⟩ := good_cong W T hC c j _ M σ hM (good_of_isTr W T hinj hC.hπ A c h).2
        (good_of_isTr W T hinj hC.hπ A c h').2
      exact satP_JJ W hSP hA hC.hπ T hTc c j _ M _ ((Formalism.MainNotions.ArcLiftingSetup.Pp W T c j).sub_mem (hTP h) (hTP h')) N hN
    have clC : ∀ w τ, Formalism.MainNotions.ArcLiftingSetup.InI W T c w → Formalism.MainNotions.ArcLiftingSetup.IsTr W A T c w τ →
        Formalism.MainNotions.ArcLiftingSetup.InFNc W T (c + (j : ZMod n)) (W.π₀ ^ M)
          (W.γ T (Formalism.MainNotions.ArcLiftingSetup.lA W ^ σ • ((W.φD T) ^ j) w - τ) -
            (Formalism.MainNotions.ArcLiftingSetup.lA W ^ σ • ((W.φD T) ^ j) w - τ)) := fun w τ hw h =>
      gamma_clause W T hC hSAT hA hTc A c hM hfirst hw (hTP h) (good_of_isTr W T hinj hC.hπ A c h).2
    refine ⟨hfirst, fun w hw => ⟨exTau w hw, fun τ τ' h h' => clB w τ τ' h h',
      fun τ h => clC w τ hw h, ?_, ?_, ?_, ?_⟩, ?_⟩
    ·
      obtain ⟨τ, h⟩ := exTau w hw
      obtain ⟨x, hx⟩ := hc3 (c + (j : ZMod n)) _ (y_letter W T c j σ hw.1 (hTP h))
        (y_Δ W T c j σ hw.2.1 (hTP h)) (clC w τ hw h)
      exact ⟨x, τ, h, hx⟩
    ·
      rintro x x' ⟨τ₁, h₁, hx⟩ ⟨τ₂, h₂, hx'⟩
      have hd := clB w τ₂ τ₁ h₂ h₁
      have hdP : τ₂ - τ₁ ∈ Formalism.MainNotions.ArcLiftingSetup.Pp W T c j := (Formalism.MainNotions.ArcLiftingSetup.Pp W T c j).sub_mem (hTP h₂) (hTP h₁)
      have h0 := hc5 (c + (j : ZMod n)) (τ₂ - τ₁) (Pp_letter W T c j _ hdP) (Pp_Δ W T c j _ hdP)
        (InFNc_of_FP W T A c hfirst hd)
      have hsum := hc4 (c + (j : ZMod n)) _ _ x' 0 (y_letter W T c j σ hw.1 (hTP h₂))
        (Pp_letter W T c j _ hdP) hx' h0
      rw [show Formalism.MainNotions.ArcLiftingSetup.lA W ^ σ • ((W.φD T) ^ j) w - τ₂ + (τ₂ - τ₁) =
        Formalism.MainNotions.ArcLiftingSetup.lA W ^ σ • ((W.φD T) ^ j) w - τ₁ by abel, add_zero] at hsum
      exact cls_unique W T M hq hc1 hc2 hx hsum
    ·
      intro hw0
      obtain ⟨u0, hu0, hu0c, hwu⟩ := hw0
      obtain ⟨u, hu, -, -, -, hu1⟩ := hC.Tr2 j 1
      have hτ : Formalism.MainNotions.ArcLiftingSetup.InFP W T c j W.π₀ (Formalism.MainNotions.ArcLiftingSetup.lA W ^ σ • ((W.φD T) ^ j) w) := by
        refine ⟨(Formalism.MainNotions.ArcLiftingSetup.lA W ^ σ * u *
            ∏ k ∈ Finset.range j, Formalism.MainNotions.LiftingTheory.pk W k ^ ((PD.p - 1) * 1)) • ((W.φD T) ^ j) u0,
          Pp_gen W T c j ?_ (InNΔi_of W T c hu0 hu0c), ?_⟩
        · exact W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.pow_mem (lA_mem W) _) hu)
            (W.AΔ.prod_mem fun k _ => W.AΔ.pow_mem (pk_mem_AΔ W hC.hπ k) _)
        · rw [hwu, φpow_smul, smul_smul, smul_smul, ← pow_one ((W.φA ^ j) W.π₀), hu1]
          congr 1; ring
      have hG := good_self W T c j (2 * A.G₀) M σ ⟨u0, InNΔi_of W T c hu0 hu0c, hwu⟩
      refine ⟨_, mkTr W hinj hO2 h9 hH hTr hA T hTc A hM c (Z_of_InI W T c hw) hτ hG, ?_⟩
      rw [sub_self]
      exact hc5 (c + (j : ZMod n)) 0 (smul_zero _) (fun δ _ => map_zero _)
        (InFNc_zero W T (c + (j : ZMod n)) (W.π₀ ^ M))
    ·
      rintro Λ' x hΛ' ⟨n', hn', hn'c, hΛw⟩ ⟨τ, h, hx⟩
      have hφΛ : (W.φA ^ j) Λ' ∈ W.AΔ := PhiPowers.φA_pow_mem_AΔ W (Ps_le_AΔ W hC.hπ hΛ') j
      refine hF2 hA A.h M hlt T hTc hJ (c + (j : ZMod n)) _ x
        ((∏ s ∈ Finset.range j, Formalism.MainNotions.ArcLiftingSetup.ps W s ^ A.G₀) * (W.φA ^ j) Λ')
        (Submonoid.mul_mem _ (prodPs_mem W j A.G₀) (φ_Ps W j hΛ'))
        (y_letter W T c j σ hw.1 (hTP h)) ?_ hx
      have hmem : Formalism.MainNotions.ArcLiftingSetup.lA W ^ σ • ((W.φD T) ^ j) n' - (W.φA ^ j) Λ' • τ ∈
          Formalism.MainNotions.ArcLiftingSetup.Pp W T c j :=
        (Formalism.MainNotions.ArcLiftingSetup.Pp W T c j).sub_mem
          (Pp_smul W T c j (W.AΔ.pow_mem (lA_mem W) _) _ (Pp_phi W T c j (InNΔi_of W T c hn' hn'c)))
          (Pp_smul W T c j hφΛ _ (hTP h))
      convert (hfirst _ hmem).2 using 1
      rw [mul_smul, smul_sub, smul_comm ((W.φA ^ j) Λ') (Formalism.MainNotions.ArcLiftingSetup.lA W ^ σ), ← φpow_smul, hΛw,
        one_smul]
    ·
      rintro w₁ w₂ x₁ x₂ hw₁ hw₂ ⟨τ₁, h₁, hx₁⟩ ⟨τ₂, h₂, hx₂⟩
      have g₁ := good_of_isTr W T hinj hC.hπ A c h₁
      have g₂ := good_of_isTr W T hinj hC.hπ A c h₂
      obtain ⟨z₁, hz₁, e₁⟩ := Z_of_InI W T c hw₁
      obtain ⟨z₂, hz₂, e₂⟩ := Z_of_InI W T c hw₂
      have hZ : ∃ z', Formalism.MainNotions.LiftingTheory.InNΔi W T c z' ∧ W.γ T (w₁ + w₂) - (w₁ + w₂) = W.π₀ • z' :=
        ⟨z₁ + z₂, InNΔi_add W T c hz₁ hz₂, by rw [map_add, smul_add, ← e₁, ← e₂]; abel⟩
      refine ⟨τ₁ + τ₂, mkTr W hinj hO2 h9 hH hTr hA T hTc A hM c hZ
        (inMultiple_add W T c j _ g₁.1 g₂.1) (good_add W T c j _ M σ g₁.2 g₂.2), ?_⟩
      have := hc4 (c + (j : ZMod n)) _ _ x₁ x₂ (y_letter W T c j σ hw₁.1 (hTP h₁))
        (y_letter W T c j σ hw₂.1 (hTP h₂)) hx₁ hx₂
      convert this using 2
      rw [map_add, smul_add]; abel
  ·
    rintro T T' f hT hT' w x hw ⟨τ, h, hx⟩
    have hTc : IsCrys PD T.ρ := hT.1
    have hT'c : IsCrys PD T'.ρ := hT'.1
    have hC := ctx_of W hinj hO2 h9 hH hTr hA T hTc
    have g := good_of_isTr W T hinj hC.hπ A c h
    obtain ⟨z, hz, e⟩ := Z_of_InI W T c hw
    have hZ : ∃ z', Formalism.MainNotions.LiftingTheory.InNΔi W T' c z' ∧ W.γ T' (W.map f w) - W.map f w = W.π₀ • z' :=
      ⟨W.map f z, InNΔi_map W f hTc hT'c c hz, by
        rw [← mapA_smul, ← e, map_sub]
        congr 1
        exact (W.map_γ f W.gam w).symm⟩
    refine ⟨W.map f τ, mkTr W hinj hO2 h9 hH hTr hA T' hT'c A hM c hZ (inMultiple_map W f hTc hT'c c j _ g.1)
      (good_map W f hTc hT'c c j _ M σ g.2), ?_⟩
    have hP : τ ∈ Formalism.MainNotions.ArcLiftingSetup.Pp W T c j := mem_Pp_of_inMultiple W T c j hC.hπ g.1
    have := (hF.2 T T' f hTc hT'c (jumpsLe_of_win W A hAok T hT) (jumpsLe_of_win W A hAok T' hT')
      (c + (j : ZMod n)) _ x (y_letter W T c j σ hw.1 hP) hx)
    convert this using 2
    rw [map_sub, mapA_smul, map_φpow]

end Formalism.MainNotions.UnusedSlot80.Relay2

noncomputable section

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem relay_general_case_of_admissible (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (h : AdmRelayA D HW F) :
    RelayArcLifting D HW F := by
  obtain ⟨h5, h9, hH, hTr, hS, hF1, hF2⟩ := h
  intro l _ K LL hG h1 h2
  exact Relay2.relayCore_of ((HW l).W K 1 LL hG) Subtype.val_injective
    (fun x hx => ⟨⟨x, ((D.loc l).v_O LL x).1 hx⟩, rfl⟩) (h9 l K 1 LL hG) (h5 l K 1 LL hG)
    (hH l K 1 LL hG) (hTr l K 1 LL hG) (hS l K LL hG h1 h2)
    (SatPW.satPCore_of ((HW l).W K 1 LL hG) Subtype.val_injective (fun T hT => h9 l K 1 LL hG T hT))
    (hF1 l K LL hG h1 h2) (hF2 l K LL hG h1 h2)

theorem relay_general_statement (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : RelayTheoremArcLifting D HW F :=
  relay_general_case_of_admissible D HW F

end Formalism.MainNotions.UnusedSlot80
