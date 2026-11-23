import Formalism.AdmissibleDesigns.FiniteClassesContinuousLattice
import Formalism.WeaklyAdmissibleFiltrations.PhtGalois

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions

namespace Formalism.MainNotions.N.KDim

open Formalism.MainNotions.N.KHf

section Trans

variable {O : Type} [CommRing O] [IsDomain O] {LL : Type} [Field LL] [TopologicalSpace LL]
  (e : FractionRing O ≃+* LL) {Qp : Type} [Field Qp] [Algebra Qp LL]
  {Γ G : Type} [Group Γ] [Group G] [TopologicalSpace G] {K₀ Kk B BdR : Type} [Field K₀] [Field Kk]
    [Algebra Qp K₀] [Algebra Qp Kk] [Algebra K₀ Kk] [IsScalarTower Qp K₀ Kk]
    [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra Kk BdR] [IsScalarTower Qp Kk BdR]
    [IsScalarTower K₀ Kk BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ Kk B BdR) (ι : G →* Γ)
  {V : Type} [AddCommGroup V] [Module (FractionRing O) V] [Module O V] [IsScalarTower O (FractionRing O) V]
  (ρ : Representation O Γ V)

def cobK : V →ₗ[FractionRing O] (Γ → V) where
  toFun v γ := ρ γ v - v
  map_add' u v := by
    funext γ
    simp only [map_add, Pi.add_apply]
    abel
  map_smul' k v := by
    funext γ
    simp only [Pi.smul_apply, RingHom.id_apply, smul_sub]
    rw [smulK (ρ γ) k v]

def fwd : ↥(finZ e PD ρ ι) →ₛₗ[(e : FractionRing O →+* LL)] ↥(finiteCocycles PD (repL e ρ ι)) where
  toFun c := ⟨fun g => (c.1 (ι g) : TrV e V), c.2⟩
  map_add' _ _ := rfl
  map_smul' k c := by
    apply Subtype.ext
    funext g
    show k • c.1 (ι g) = e.symm (e k) • c.1 (ι g)
    rw [RingEquiv.symm_apply_apply]

variable {ι} (hι : Function.Bijective ι)
include hι

def bwd : ↥(finiteCocycles PD (repL e ρ ι)) →ₛₗ[(e.symm : LL →+* FractionRing O)] ↥(finZ e PD ρ ι) where
  toFun c := ⟨fun γ => (c.1 ((Equiv.ofBijective ι hι).symm γ) : V), by
    show (fun g => (c.1 ((Equiv.ofBijective ι hι).symm (ι g)) : TrV e V)) ∈ finiteCocycles PD (repL e ρ ι)
    have h : (fun g => (c.1 ((Equiv.ofBijective ι hι).symm (ι g)) : TrV e V)) = c.1 := by
      funext g
      have : (Equiv.ofBijective ι hι).symm (ι g) = g := (Equiv.ofBijective ι hι).symm_apply_apply g
      rw [this]
    rw [h]
    exact c.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem bwd_fwd (c : ↥(finZ e PD ρ ι)) : bwd e PD ρ hι (fwd e PD ι ρ c) = c := by
  apply Subtype.ext
  funext γ
  exact congrArg c.1 ((Equiv.ofBijective ι hι).apply_symm_apply γ)

theorem fwd_bwd (c : ↥(finiteCocycles PD (repL e ρ ι))) : fwd e PD ι ρ (bwd e PD ρ hι c) = c := by
  apply Subtype.ext
  funext g
  exact congrArg c.1 ((Equiv.ofBijective ι hι).symm_apply_apply g)

theorem mem_cob_iff (c : ↥(finZ e PD ρ ι)) :
    c.1 ∈ LinearMap.range (cobK ρ) ↔ (fwd e PD ι ρ c).1 ∈ B1 (repL e ρ ι) := by
  rw [B1, LinearMap.mem_range, LinearMap.mem_range]
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨(show TrV e V from v), ?_⟩
    funext g
    exact congrFun hv (ι g)
  · rintro ⟨w, hw⟩
    refine ⟨(show V from w), ?_⟩
    funext γ
    obtain ⟨g, rfl⟩ := hι.2 γ
    exact congrFun hw g

def fwdQ : (↥(finZ e PD ρ ι) ⧸ (LinearMap.range (cobK ρ)).comap (finZ e PD ρ ι).subtype) →ₛₗ[(e : FractionRing O →+* LL)]
    FiniteCohomology PD (repL e ρ ι) :=
  Submodule.mapQ ((LinearMap.range (cobK ρ)).comap (finZ e PD ρ ι).subtype)
    ((B1 (repL e ρ ι)).comap (finiteCocycles PD (repL e ρ ι)).subtype) (fwd e PD ι ρ)
    (by intro c hc; exact (mem_cob_iff e PD ρ hι c).1 hc)

def quotEquiv : (↥(finZ e PD ρ ι) ⧸ (LinearMap.range (cobK ρ)).comap (finZ e PD ρ ι).subtype) ≃+
    FiniteCohomology PD (repL e ρ ι) where
  toFun := fwdQ e PD ρ hι
  invFun := Submodule.mapQ ((B1 (repL e ρ ι)).comap (finiteCocycles PD (repL e ρ ι)).subtype)
    ((LinearMap.range (cobK ρ)).comap (finZ e PD ρ ι).subtype) (bwd e PD ρ hι) (by
    intro c hc
    have h : (fwd e PD ι ρ (bwd e PD ρ hι c)).1 ∈ B1 (repL e ρ ι) := by
      rw [fwd_bwd]
      exact hc
    exact (mem_cob_iff e PD ρ hι _).2 h)
  left_inv x := by
    induction x using Submodule.Quotient.induction_on with
    | H c => exact congrArg Submodule.Quotient.mk (bwd_fwd e PD ρ hι c)
  right_inv x := by
    induction x using Submodule.Quotient.induction_on with
    | H c => exact congrArg Submodule.Quotient.mk (fwd_bwd e PD ρ hι c)
  map_add' x y := map_add (fwdQ e PD ρ hι) x y

theorem rank_finQuot :
    Module.rank (FractionRing O)
        (↥(finZ e PD ρ ι) ⧸ (LinearMap.range (cobK ρ)).comap (finZ e PD ρ ι).subtype) =
      Module.rank LL (FiniteCohomology PD (repL e ρ ι)) :=
  rank_eq_of_equiv_equiv e (quotEquiv e PD ρ hι) e.bijective
    (fun k x => (fwdQ e PD ρ hι).map_smulₛₗ k x)

omit hι in
theorem mem_H0V' {W : Type} [AddCommGroup W] [Module LL W] (σ : Representation LL G W) (v : W) :
    v ∈ H0V σ ↔ ∀ g, σ g v = v := by
  simp only [H0V, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero]

def cohomZeroEquivContinuous : ↥(LinearMap.ker (cobK ρ)) ≃+ ↥(H0V (repL e ρ ι)) where
  toFun v := ⟨(v.1 : TrV e V), by
    refine (mem_H0V' (repL e ρ ι) _).2 (fun g => ?_)
    have h := congrFun (LinearMap.mem_ker.mp v.2) (ι g)
    exact sub_eq_zero.mp h⟩
  invFun v := ⟨(show V from v.1), by
    show (show V from v.1) ∈ LinearMap.ker (cobK ρ)
    rw [LinearMap.mem_ker]
    funext γ
    obtain ⟨g, rfl⟩ := hι.2 γ
    have h2 := (mem_H0V' (repL e ρ ι) _).1 v.2 g
    exact sub_eq_zero.mpr h2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

theorem rank_invariants_eq :
    Module.rank (FractionRing O) ↥(LinearMap.ker (cobK ρ)) = Module.rank LL ↥(H0V (repL e ρ ι)) :=
  rank_eq_of_equiv_equiv e (cohomZeroEquivContinuous e ρ hι) e.bijective (fun k v => by
    apply Subtype.ext
    show k • (v.1 : V) = e.symm (e k) • (v.1 : V)
    rw [RingEquiv.symm_apply_apply])

theorem finrank_invariants_eq :
    Module.finrank (FractionRing O) ↥(LinearMap.ker (cobK ρ)) = Module.finrank LL ↥(H0V (repL e ρ ι)) := by
  exact congrArg Cardinal.toNat (rank_invariants_eq e ρ hι)

omit hι [TopologicalSpace LL] in

theorem finDim_TrV [FiniteDimensional (FractionRing O) V] : FiniteDimensional LL (TrV e V) := by
  have h : Module.rank (FractionRing O) V = Module.rank LL (TrV e V) :=
    rank_eq_of_equiv_equiv e (AddEquiv.refl V) e.bijective (fun k v => by
      show k • v = e.symm (e k) • v
      rw [RingEquiv.symm_apply_apply])
  have h1 : Module.rank (FractionRing O) V < Cardinal.aleph0 := Module.rank_lt_aleph0_iff.mpr inferInstance
  rw [h] at h1
  exact Module.rank_lt_aleph0_iff.mp h1

end Trans

section Count

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [Fintype (K →ₐ[Qp] LL)]

def FilLow {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) : Prop :=
  ∀ τ : K →ₐ[Qp] LL, FiniteDimensional LL ↥(DdRE PD ρ τ) ∧
    ∃ lo : ℤ, lo ≤ 0 ∧ ∀ a, a ≤ lo → FildR PD ρ τ a = DdRE PD ρ τ

private theorem sum_Ico_sub_succ_eq_telescope (f : ℤ → ℤ) : ∀ (n : ℕ) (lo : ℤ), lo + n = 0 →
    ∑ a ∈ Finset.Ico lo 0, (f a - f (a + 1)) = f lo - f 0 := by
  intro n
  induction n with
  | zero =>
    intro lo h
    have h0 : lo = 0 := by omega
    subst h0
    simp
  | succ k ih =>
    intro lo h
    have hs : Finset.Ico lo 0 = insert lo (Finset.Ico (lo + 1) 0) := by
      ext x
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    have hn : lo ∉ Finset.Ico (lo + 1) 0 := by
      simp only [Finset.mem_Ico]
      omega
    rw [hs, Finset.sum_insert hn, ih (lo + 1) (by omega)]
    ring

theorem negdim_eq {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (hfin : FiniteDimensional LL ↥(DdRE PD ρ τ))
    (lo : ℤ) (hlo : lo ≤ 0) (hF : FildR PD ρ τ lo = DdRE PD ρ τ) :
    (finrank LL ↥(DdRE PD ρ τ) : ℤ) - finrank LL ↥(FildR PD ρ τ 0) =
      ∑ a ∈ Finset.Ico lo 0, multV PD ρ τ a := by
  have hn : lo + (((-lo).toNat : ℕ) : ℤ) = 0 := by
    rw [Int.toNat_of_nonneg (by omega)]
    ring
  have h := sum_Ico_sub_succ_eq_telescope (fun a => (finrank LL ↥(FildR PD ρ τ a) : ℤ)) (-lo).toNat lo hn
  rw [← hF]
  exact h.symm

theorem count_eq (hBK : BlochKatoDim PD LL) (hS : Splits LL (K := K) (Qp := Qp))
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] [TopologicalSpace V] [IsModuleTopology LL V] [IsTopologicalAddGroup V]
    [ContinuousConstSMul LL V] (ρ : Representation LL G V)
    {W : Type} [AddCommGroup W] [Module LL W] [Module Qp W] [IsScalarTower Qp LL W]
    [FiniteDimensional LL W] [TopologicalSpace W] [IsModuleTopology LL W] [IsTopologicalAddGroup W]
    [ContinuousConstSMul LL W] (ρW : Representation LL G W)
    (hcV : ∀ x, Continuous fun g => ρ g x) (hcW : ∀ x, Continuous fun g => ρW g x)
    (hcrV : IsCrys PD ρ) (hcrW : IsCrys PD ρW) (hlowV : FilLow PD ρ) (hlowW : FilLow PD ρW)
    (hneg : ∀ τ a, a < 0 → multV PD ρ τ a = multV PD ρW τ a) (h0W : H0V ρW = ⊥) :
    (finrank LL (FiniteCohomology PD ρ) : ℤ) = finrank LL ↥(H0V ρ) + finrank LL (FiniteCohomology PD ρW) := by
  have hV := hBK hS V ρ hcV hcrV
  have hW := hBK hS W ρW hcW hcrW
  have hsum : ∀ τ : K →ₐ[Qp] LL, ((finrank LL ↥(DdRE PD ρ τ) : ℤ) - finrank LL ↥(FildR PD ρ τ 0)) =
      ((finrank LL ↥(DdRE PD ρW τ) : ℤ) - finrank LL ↥(FildR PD ρW τ 0)) := by
    intro τ
    obtain ⟨hfV, loV, hloV, hFV⟩ := hlowV τ
    obtain ⟨hfW, loW, hloW, hFW⟩ := hlowW τ
    rw [negdim_eq PD ρ τ hfV (min loV loW) (le_trans (min_le_left _ _) hloV) (hFV _ (min_le_left _ _)),
      negdim_eq PD ρW τ hfW (min loV loW) (le_trans (min_le_left _ _) hloV) (hFW _ (min_le_right _ _))]
    apply Finset.sum_congr rfl
    intro a ha
    exact hneg τ a (Finset.mem_Ico.mp ha).2
  rw [hV, hW, Finset.sum_congr rfl (fun τ _ => hsum τ), h0W]
  simp

theorem rank_le_count (hBK : BlochKatoDim PD LL) (hS : Splits LL (K := K) (Qp := Qp))
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] [TopologicalSpace V] [IsModuleTopology LL V] [IsTopologicalAddGroup V]
    [ContinuousConstSMul LL V] (ρ : Representation LL G V)
    {W : Type} [AddCommGroup W] [Module LL W] [Module Qp W] [IsScalarTower Qp LL W]
    [FiniteDimensional LL W] [TopologicalSpace W] [IsModuleTopology LL W] [IsTopologicalAddGroup W]
    [ContinuousConstSMul LL W] (ρW : Representation LL G W)
    (hcV : ∀ x, Continuous fun g => ρ g x) (hcW : ∀ x, Continuous fun g => ρW g x)
    (hcrV : IsCrys PD ρ) (hcrW : IsCrys PD ρW) (hlowV : FilLow PD ρ) (hlowW : FilLow PD ρW)
    (hneg : ∀ τ a, a < 0 → multV PD ρ τ a = multV PD ρW τ a) (h0W : H0V ρW = ⊥)
    (hfin : FiniteDimensional LL (FiniteCohomology PD ρ)) :
    Module.rank LL (FiniteCohomology PD ρ) ≤ ((finrank LL (FiniteCohomology PD ρW) + finrank LL ↥(H0V ρ) : ℕ) : Cardinal) := by
  have h := count_eq PD hBK hS ρ ρW hcV hcW hcrV hcrW hlowV hlowW hneg h0W
  have h' : finrank LL (FiniteCohomology PD ρ) = finrank LL (FiniteCohomology PD ρW) + finrank LL ↥(H0V ρ) := by omega
  rw [← h']
  have hlt : Module.rank LL (FiniteCohomology PD ρ) < Cardinal.aleph0 := Module.rank_lt_aleph0_iff.mpr hfin
  first
    | exact le_of_eq (Module.finrank_eq_rank (R := LL) (M := FiniteCohomology PD ρ)).symm
    | exact (Cardinal.cast_toNat_of_lt_aleph0 hlt).symm.le

end Count

section Low

open Classical

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem fil_anti : Antitone PD.Fil := by
  exact antitone_int_of_succ_le PD.Fil_anti

theorem filV_mono {a b : ℤ} (h : a ≤ b) : FilV PD (LL := LL) (V := V) b ≤ FilV PD a := by
  have hle : (PD.Fil b).restrictScalars Qp ≤ (PD.Fil a).restrictScalars Qp := fun x hx => fil_anti PD h hx
  intro x hx
  obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
  clear hx
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | tmul v f => exact LinearMap.mem_range.mpr ⟨v ⊗ₜ[Qp] Submodule.inclusion hle f, rfl⟩
  | add y z hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz

theorem exists_filV (x : TensorProduct Qp V BdR) : ∃ a, x ∈ FilV PD (LL := LL) a := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | tmul v f =>
    obtain ⟨a, ha⟩ := PD.Fil_exh f
    exact ⟨a, LinearMap.mem_range.mpr ⟨v ⊗ₜ[Qp] (⟨f, ha⟩ : ↥((PD.Fil a).restrictScalars Qp)), rfl⟩⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨min a b, Submodule.add_mem _ (filV_mono PD (min_le_left a b) ha)
      (filV_mono PD (min_le_right a b) hb)⟩

theorem exists_low_finset (s : Finset (TensorProduct Qp V BdR)) :
    ∃ a : ℤ, a ≤ 0 ∧ ∀ x ∈ s, x ∈ FilV PD (LL := LL) a := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, le_refl 0, fun x hx => by simp at hx⟩
  | @insert x s hxs ih =>
    obtain ⟨a, ha0, ha⟩ := ih
    obtain ⟨b, hb⟩ := exists_filV PD (LL := LL) x
    refine ⟨min a b, le_trans (min_le_left a b) ha0, fun y hy => ?_⟩
    rcases Finset.mem_insert.mp hy with rfl | hy'
    · exact filV_mono PD (min_le_right a b) hb
    · exact filV_mono PD (min_le_left a b) (ha y hy')

variable (ρ : Representation LL G V)

theorem low_of_fin (τ : K →ₐ[Qp] LL) (hfin : FiniteDimensional LL ↥(DdRE PD ρ τ)) :
    ∃ lo : ℤ, lo ≤ 0 ∧ ∀ a, a ≤ lo → FildR PD ρ τ a = DdRE PD ρ τ := by
  let b := Module.finBasis LL ↥(DdRE PD ρ τ)
  obtain ⟨lo, hlo, hs⟩ := exists_low_finset PD (LL := LL)
    (Finset.univ.image (fun j => ((b j : ↥(DdRE PD ρ τ)) : TensorProduct Qp V BdR)))
  refine ⟨lo, hlo, fun a ha => ?_⟩
  have hb : ∀ j, ((b j : ↥(DdRE PD ρ τ)) : TensorProduct Qp V BdR) ∈ FilV PD (LL := LL) a := fun j =>
    filV_mono PD ha (hs _ (Finset.mem_image_of_mem _ (Finset.mem_univ j)))
  unfold FildR
  apply inf_eq_left.mpr
  intro y hy
  have hspan : Submodule.span LL (Set.range b) ≤ (FilV PD (LL := LL) a).comap (DdRE PD ρ τ).subtype := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hb j
  rw [b.span_eq] at hspan
  exact hspan (Submodule.mem_top (x := (⟨y, hy⟩ : ↥(DdRE PD ρ τ))))

theorem filLow_of_dR [FiniteDimensional LL V] (hV : 0 < finrank LL V)
    (hDR : finrank LL ↥(DdR PD ρ) = finrank Qp K * finrank LL V) : FilLow PD ρ := by
  intro τ
  haveI := PD.finK
  have hK : 0 < Module.finrank Qp K := Module.finrank_pos
  have hpos : 0 < finrank LL ↥(DdR PD ρ) := by
    rw [hDR]
    exact Nat.mul_pos hK hV
  haveI : FiniteDimensional LL ↥(DdR PD ρ) := Module.finite_of_finrank_pos hpos
  have hle : DdRE PD ρ τ ≤ DdR PD ρ := inf_le_left
  haveI hfin : FiniteDimensional LL ↥(DdRE PD ρ τ) := Submodule.finiteDimensional_of_le hle
  exact ⟨hfin, low_of_fin PD ρ τ hfin⟩

end Low

section Rec

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.NG Classical

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  {X' : Type} {d : Type} [Fintype d] [DecidableEq d]
  {R' : Subalgebra (D.nd.O i) (X' → Matrix d d (FractionRing (D.nd.O i)))} {Tc : Type} [CommRing Tc] [Algebra Tc R']
  (r : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) →* R') (χ : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) →* Tcˣ)
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

theorem col_over (l : K.Col i dc) : K.plOf i dc (K.colIdx i dc l) ∈ placesOver D.host.E (D.nd.l i) := by
  have hmem : l.1 ∈ K.plSet i dc := by
    unfold K.plSet
    simp only [Finset.mem_union]
    exact Or.inl (Or.inr l.2)
  have hidx : K.plOf i dc (K.colIdx i dc l) = l.1 := by
    unfold K.plOf K.colIdx K.idx
    rw [dif_pos hmem, dif_pos ((K.plSet i dc).equivFin ⟨l.1, hmem⟩).isLt]
    simp
  rw [hidx]
  exact (dc.cover l.1).mp (Or.inr l.2)

theorem colD_eq (x' : X') (n : ℕ) :
    letI := evalModO i (R' := R') x'
    haveI := evalTower i (R' := R') x'
    colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) d R' x') r χ (Γn i dc n) =
      cobK (repE i dc r χ x' n) := by
  first
    | rfl
    | exact LinearMap.ext fun v => funext fun g => rfl

abbrev repX (x' : X') (n : ℕ) (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) :
    letI := evalModO i (R' := R') x'
    Representation (Br.LL D.nbr i _ hn) (Br.G D.nbr i _ hn)
      (TrV (eK (D.nbr i _ hn)) (EvalSp (D.nd.O i) d R' x')) :=
  letI := evalModO i (R' := R') x'
  haveI := evalTower i (R' := R') x'
  repL (eK (D.nbr i _ hn)) (repE i dc r χ x' n) (Br.iota D.nbr i _ hn)

abbrev repW (n : ℕ) (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) :
    Representation (Br.LL D.nbr i _ hn) (Br.G D.nbr i _ hn) (Fin D.R.r → Br.LL D.nbr i _ hn) :=
  matRep (Br.loc D.nbr i _ hn (WpO D.nd i ρ π))

def ContX (x' : X') (l : K.Col i dc) : Prop :=
  letI := evalModO i (R' := R') x'
  ∀ v, Continuous fun g => repX i dc r χ x' (K.colIdx i dc l) (col_over i dc l) g v

theorem contX_of_orbC (x' : X') (l : K.Col i dc) :
    letI := evalModO i (R' := R') x'
    haveI := evalTower i (R' := R') x'
    OrbC i dc (repE i dc r χ x' (K.colIdx i dc l)) → ContX i dc r χ x' l := by
  intro h
  exact h (col_over i dc l)

def CrysX (x' : X') (l : K.Col i dc) : Prop :=
  letI := evalModO i (R' := R') x'
  IsCrys (Br.PD D.loc D.nbr i _ (col_over i dc l)) (repX i dc r χ x' (K.colIdx i dc l) (col_over i dc l))

def NegX (x' : X') (l : K.Col i dc) : Prop :=
  letI := evalModO i (R' := R') x'
  ∀ τ a, a < 0 →
    multV (Br.PD D.loc D.nbr i _ (col_over i dc l)) (repX i dc r χ x' (K.colIdx i dc l) (col_over i dc l)) τ a =
      multV (Br.PD D.loc D.nbr i _ (col_over i dc l)) (repW i dc ρ π (K.colIdx i dc l) (col_over i dc l)) τ a

def FilLowX (x' : X') (l : K.Col i dc) : Prop :=
  letI := evalModO i (R' := R') x'
  FilLow (Br.PD D.loc D.nbr i _ (col_over i dc l)) (repX i dc r χ x' (K.colIdx i dc l) (col_over i dc l))

def FinX (x' : X') (l : K.Col i dc) : Prop :=
  letI := evalModO i (R' := R') x'
  FiniteDimensional (Br.LL D.nbr i _ (col_over i dc l))
    (FiniteCohomology (Br.PD D.loc D.nbr i _ (col_over i dc l)) (repX i dc r χ x' (K.colIdx i dc l) (col_over i dc l)))

def GoodW (l : K.Col i dc) : Prop :=
  IsCrys (Br.PD D.loc D.nbr i _ (col_over i dc l)) (repW i dc ρ π (K.colIdx i dc l) (col_over i dc l)) ∧
    (∀ v, Continuous fun g => repW i dc ρ π (K.colIdx i dc l) (col_over i dc l) g v) ∧
    FilLow (Br.PD D.loc D.nbr i _ (col_over i dc l)) (repW i dc ρ π (K.colIdx i dc l) (col_over i dc l))

omit [DecidableEq d] in

theorem invariants_twist_eq_bot (rX : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (hG2 : TruncatedSeriesCountingIdentities.admG2 i rX ρ π)
    (n : ℕ) (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) :
    H0V (repW i dc ρ π n hn) = ⊥ := by
  have h := (hG2 (K.plOf i dc n) hn (TruncatedSeriesCountingIdentities.CoefExt.self (D := D) (i := i) (hw := hn))).1
  exact h.2.2.2.2.2.1

end Rec

section Main

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.NG Classical

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  {X' : Type} {d : Type} [Fintype d] [DecidableEq d]
  {R' : Subalgebra (D.nd.O i) (X' → Matrix d d (FractionRing (D.nd.O i)))} {Tc : Type} [CommRing Tc] [Algebra Tc R']
  (r : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) →* R') (χ : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) →* Tcˣ)
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

private theorem lx_col_eq (x' : X') (l : K.Col i dc) :
    letI := evalModO i (R' := R') x'
    haveI := evalTower i (R' := R') x'
    Lx i dc r χ x' l = finZ (eK (D.nbr i _ (col_over i dc l))) (Br.PD D.loc D.nbr i _ (col_over i dc l))
      (repE i dc r χ x' (K.colIdx i dc l)) (Br.iota D.nbr i _ (col_over i dc l)) := by
  unfold Lx fZ
  rw [dif_pos (col_over i dc l)]

private theorem jK_colIdx_eq_finrank_cohomology (l : K.Col i dc) :
    jK i dc ρ π (K.colIdx i dc l) = Module.finrank (Br.LL D.nbr i _ (col_over i dc l))
      (FiniteCohomology (Br.PD D.loc D.nbr i _ (col_over i dc l))
        (repW i dc ρ π (K.colIdx i dc l) (col_over i dc l))) := by
  unfold jK
  rw [dif_pos (col_over i dc l)]
  rfl

private theorem iota_bijective_col (l : K.Col i dc) :
    Function.Bijective (Br.iota D.nbr i _ (col_over i dc l)) :=
  (D.nbr i _ (col_over i dc l)).e.symm.bijective

set_option maxHeartbeats 800000 in

theorem dimLx_of (rX : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (x' : X') (l : K.Col i dc)
    (hBK : TruncatedSeriesCountingIdentities.admBK i) (hG2 : TruncatedSeriesCountingIdentities.admG2 i rX ρ π)
    (hc : ContX i dc r χ x' l) (hcr : CrysX i dc r χ x' l) (hneg : NegX i dc r χ ρ π x' l)
    (hlow : FilLowX i dc r χ x' l) (hfin : FinX i dc r χ x' l) (hW : GoodW i dc ρ π l) :
    DimLx i dc r χ (jK i dc ρ π) x' l := by
  have hw := col_over i dc l
  letI := evalModO i (R' := R') x'
  haveI := evalTower i (R' := R') x'
  have hι := iota_bijective_col i dc l
  unfold DimLx
  rw [lx_col_eq i dc r χ x' l, colD_eq i dc r χ x' (K.colIdx i dc l), jK_colIdx_eq_finrank_cohomology i dc ρ π l,
    rank_finQuot (eK (D.nbr i _ hw)) (Br.PD D.loc D.nbr i _ hw) (repE i dc r χ x' (K.colIdx i dc l)) hι,
    finrank_invariants_eq (eK (D.nbr i _ hw)) (repE i dc r χ x' (K.colIdx i dc l)) hι]
  haveI := finDim_TrV (V := EvalSp (D.nd.O i) d R' x') (eK (D.nbr i _ hw))
  have hBK' : BlochKatoDim (Br.PD D.loc D.nbr i _ hw) (Br.LL D.nbr i _ hw) := (hBK (K.plOf i dc (K.colIdx i dc l)) hw (TruncatedSeriesCountingIdentities.CoefExt.self (D := D) (i := i) (hw := hw))).2.1
  have hS : Splits (Br.LL D.nbr i _ hw) (K := Br.Kw D.nbr i _ hw) (Qp := ℚ_[D.nd.l i]) :=
    LargeLevelLemmas.splits_coef (TruncatedSeriesCountingIdentities.CoefExt.self (D := D) (i := i) (hw := hw))
  exact rank_le_count (Br.PD D.loc D.nbr i _ hw) hBK' hS
    (repX i dc r χ x' (K.colIdx i dc l) hw) (repW i dc ρ π (K.colIdx i dc l) hw)
    hc hW.2.1 hcr hW.1 hlow hW.2.2 hneg (invariants_twist_eq_bot i dc ρ π rX hG2 (K.colIdx i dc l) hw) hfin

end Main

section Dr

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.NG Classical

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  {X' : Type} {d : Type} [Fintype d] [DecidableEq d]
  {R' : Subalgebra (D.nd.O i) (X' → Matrix d d (FractionRing (D.nd.O i)))} {Tc : Type} [CommRing Tc] [Algebra Tc R']
  (r : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) →* R') (χ : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) →* Tcˣ)
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

theorem finrank_TrV (x' : X') {LL : Type} [Field LL] (e : FractionRing (D.nd.O i) ≃+* LL) :
    Module.finrank LL (TrV e (EvalSp (D.nd.O i) d R' x')) = Fintype.card d := by
  have h : Module.rank (FractionRing (D.nd.O i)) (d → FractionRing (D.nd.O i)) =
      Module.rank LL (TrV e (EvalSp (D.nd.O i) d R' x')) :=
    rank_eq_of_equiv_equiv e (AddEquiv.refl _) e.bijective (fun k v => by
      show k • v = e.symm (e k) • v
      rw [RingEquiv.symm_apply_apply])
  have h2 : Module.finrank (FractionRing (D.nd.O i)) (d → FractionRing (D.nd.O i)) =
      Module.finrank LL (TrV e (EvalSp (D.nd.O i) d R' x')) := congrArg Cardinal.toNat h
  rw [← h2]
  first
    | simp
    | exact Module.finrank_fintype_fun_eq_card _

def grepX (x' : X') (l : K.Col i dc) (hc : ContX i dc r χ x' l) :
    GRep (Br.G D.nbr i _ (col_over i dc l)) ℚ_[D.nd.l i] (Br.LL D.nbr i _ (col_over i dc l))
      (Br.OLL D.nbr i _ (col_over i dc l)) :=
  letI := evalModO i (R' := R') x'
  haveI := evalTower i (R' := R') x'
  letI mO : Module (Br.OLL D.nbr i _ (col_over i dc l))
      (TrV (eK (D.nbr i _ (col_over i dc l))) (EvalSp (D.nd.O i) d R' x')) :=
    Module.compHom _ (algebraMap (Br.OLL D.nbr i _ (col_over i dc l)) (Br.LL D.nbr i _ (col_over i dc l)))
  haveI tO : IsScalarTower (Br.OLL D.nbr i _ (col_over i dc l)) (Br.LL D.nbr i _ (col_over i dc l))
      (TrV (eK (D.nbr i _ (col_over i dc l))) (EvalSp (D.nd.O i) d R' x')) :=
    ⟨fun a b v => by
      show (a • b) • v = (algebraMap _ (Br.LL D.nbr i _ (col_over i dc l)) a) • (b • v)
      rw [Algebra.smul_def, mul_smul]⟩
  haveI := finDim_TrV (V := EvalSp (D.nd.O i) d R' x') (eK (D.nbr i _ (col_over i dc l)))
  { V := TrV (eK (D.nbr i _ (col_over i dc l))) (EvalSp (D.nd.O i) d R' x')
    modO := mO
    towO := tO
    ρ := repX i dc r χ x' (K.colIdx i dc l) (col_over i dc l)
    cont := hc }

theorem filLowX_of (hFont : TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i) (hd : 0 < Fintype.card d) (x' : X') (l : K.Col i dc)
    (hc : ContX i dc r χ x' l) (hcr : CrysX i dc r χ x' l) : FilLowX i dc r χ x' l := by
  have hw := col_over i dc l
  have hF := (hFont (K.plOf i dc (K.colIdx i dc l)) hw (TruncatedSeriesCountingIdentities.CoefExt.self (D := D) (i := i) (hw := hw))).2.2.2
  have hDR := hF (grepX i dc r χ x' l hc) hcr
  letI := evalModO i (R' := R') x'
  haveI := evalTower i (R' := R') x'
  haveI := finDim_TrV (V := EvalSp (D.nd.O i) d R' x') (eK (D.nbr i _ hw))
  exact filLow_of_dR (Br.PD D.loc D.nbr i _ hw) (repX i dc r χ x' (K.colIdx i dc l) hw)
    (by rw [finrank_TrV]; exact hd) hDR

def grepW (l : K.Col i dc)
    (hc : ∀ v, Continuous fun g => repW i dc ρ π (K.colIdx i dc l) (col_over i dc l) g v) :
    GRep (Br.G D.nbr i _ (col_over i dc l)) ℚ_[D.nd.l i] (Br.LL D.nbr i _ (col_over i dc l))
      (Br.OLL D.nbr i _ (col_over i dc l)) where
  V := Fin D.R.r → Br.LL D.nbr i _ (col_over i dc l)
  ρ := repW i dc ρ π (K.colIdx i dc l) (col_over i dc l)
  cont := hc

theorem goodW_of (hFont : TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i) (hr : 0 < D.R.r) (l : K.Col i dc)
    (hcr : IsCrys (Br.PD D.loc D.nbr i _ (col_over i dc l)) (repW i dc ρ π (K.colIdx i dc l) (col_over i dc l)))
    (hc : ∀ v, Continuous fun g => repW i dc ρ π (K.colIdx i dc l) (col_over i dc l) g v) :
    GoodW i dc ρ π l := by
  refine ⟨hcr, hc, ?_⟩
  have hw := col_over i dc l
  have hF := (hFont (K.plOf i dc (K.colIdx i dc l)) hw (TruncatedSeriesCountingIdentities.CoefExt.self (D := D) (i := i) (hw := hw))).2.2.2
  have hDR := hF (grepW i dc ρ π l hc) hcr
  have hpos : 0 < Module.finrank (Br.LL D.nbr i _ hw) (Fin D.R.r → Br.LL D.nbr i _ hw) := by
    first
      | (rw [Module.finrank_fin_fun]; exact hr)
      | simpa using hr
  exact filLow_of_dR (Br.PD D.loc D.nbr i _ hw) (repW i dc ρ π (K.colIdx i dc l) hw) hpos hDR

end Dr

section Main2

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.NG Classical

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  {X' : Type} {d : Type} [Fintype d] [DecidableEq d]
  {R' : Subalgebra (D.nd.O i) (X' → Matrix d d (FractionRing (D.nd.O i)))} {Tc : Type} [CommRing Tc] [Algebra Tc R']
  (r : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) →* R') (χ : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) →* Tcˣ)
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

def CrysW (l : K.Col i dc) : Prop :=
  IsCrys (Br.PD D.loc D.nbr i _ (col_over i dc l)) (repW i dc ρ π (K.colIdx i dc l) (col_over i dc l))

def ContW (l : K.Col i dc) : Prop :=
  ∀ v, Continuous fun g => repW i dc ρ π (K.colIdx i dc l) (col_over i dc l) g v

theorem dimLx_of_font (rX : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (x' : X') (l : K.Col i dc)
    (hd : 0 < Fintype.card d) (hr : 0 < D.R.r)
    (hBK : TruncatedSeriesCountingIdentities.admBK i) (hG2 : TruncatedSeriesCountingIdentities.admG2 i rX ρ π) (hFont : TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i)
    (hc : ContX i dc r χ x' l) (hcr : CrysX i dc r χ x' l) (hneg : NegX i dc r χ ρ π x' l)
    (hfin : FinX i dc r χ x' l) (hcrW : CrysW i dc ρ π l) (hcW : ContW i dc ρ π l) :
    DimLx i dc r χ (jK i dc ρ π) x' l :=
  dimLx_of i dc r χ ρ π rX x' l hBK hG2 hc hcr hneg (filLowX_of i dc r χ hFont hd x' l hc hcr) hfin
    (goodW_of i dc ρ π hFont hr l hcrW hcW)

end Main2

section EvalU

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X d G : Type}
  [Fintype d] [DecidableEq d] [Group G] {t : ℕ} {bl : d → Fin (t + 1)}
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData O X d G t bl) {T : Subalgebra O (X → O)} {r₀ : G →* (X → Matrix d d O)}
  {π₀ : X} {χ₁ ε : G →* Oˣ} {g₀ : G} {eB e₁ s : X → Matrix d d O}

end EvalU

section Ident

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.NG Classical

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) {bl : Fin D.R.nV → Fin (D.R.t + 1)}
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t bl)

def phiX (x' : Dd.X') {LL : Type} [Field LL] (e : FractionRing (D.nd.O i) ≃+* LL) :
    TrV e (EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x') ≃ₗ[LL] (Fin D.R.nV → LL) where
  toFun v j := e ((show Fin D.R.nV → FractionRing (D.nd.O i) from v) j)
  invFun w := (show EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x' from fun j => e.symm (w j))
  map_add' u v := by
    funext j
    exact map_add e _ _
  map_smul' c v := by
    funext j
    show e (e.symm c * (show Fin D.R.nV → FractionRing (D.nd.O i) from v) j) = c * e _
    rw [map_mul, RingEquiv.apply_symm_apply]
  left_inv v := by
    funext j
    exact e.symm_apply_apply _
  right_inv w := by
    funext j
    exact e.apply_symm_apply _

end Ident

end Formalism.MainNotions.N.KDim
