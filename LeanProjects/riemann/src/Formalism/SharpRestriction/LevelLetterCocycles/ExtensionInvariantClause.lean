import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ExtensionClauses
import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangePreservesUnitaryOf

noncomputable section

namespace Formalism.MainNotions.UnusedSlot35.ExtCPf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.LiftingTheory

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA] [Algebra O RW]
    {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}

theorem smulO_mem (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (c : O) {x : W.DD T}
    (hx : x ∈ W.N T) : c • x ∈ W.N T := by
  rw [← algebraMap_smul (LetA O n) c x]
  exact (W.N T).smul_mem _ hx

theorem map_smulO (W : LocWach PD LL O v n) {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L)
    (c : O) (x : W.DD T) : W.map f (c • x) = c • W.map f x := by
  first
  | exact (W.map f).map_smul_of_tower c x
  | exact LinearMap.map_smul_of_tower (W.map f) c x
  | (rw [← algebraMap_smul (LetA O n) c x, ← algebraMap_smul (LetA O n) c (W.map f x)]
     exact (W.map f).map_smul _ x)
  | simp

theorem pull_cocycle (W : LocWach PD LL O v n) {T Tp : LocLat G Qp LL O} (ι : LatHom T.L Tp.L)
    (hinj : Function.Injective (W.map ι)) (g : W.Gam) (x : W.DD Tp) (y z : W.DD T)
    (hy : W.map ι y = W.φD Tp x - x) (hz : W.map ι z = W.γD Tp g x - x) :
    (W.γD T g y - y) - (W.φD T z - z) = 0 := by
  have hφ : ∀ w, W.map ι (W.φD T w) = W.φD Tp (W.map ι w) := fun w => W.map_φ ι w
  have hγ : ∀ w, W.map ι (W.γD T g w) = W.γD Tp g (W.map ι w) := fun w => W.map_γ ι g w
  apply hinj
  simp only [map_sub, map_zero, hφ, hγ, hy, hz, W.φγ_comm]
  abel

theorem coreExt_of (W : LocWach PD LL O v n) (E : EtTie W RA RW inclR φR gR πA)
    (h8 : Formalism.MainNotions.DeltaInvariantLattices.WachMaxJumpBound W) (hH : Formalism.MainNotions.ElementDenominator.coreHerrExt W) : coreExt W := by
  unfold Formalism.MainNotions.LiftingTheory.coreExt
  intro T Tp ι π Mi hi hT hTp hJ c hc hext k hk
  unfold Formalism.MainNotions.LiftingTheory.InImgA at hk
  obtain ⟨e, he, hspan, hφe, hγe, x, hx, hxe⟩ := hk
  unfold Formalism.MainNotions.ElementDenominator.coreHerrExt at hH
  obtain ⟨u, hu⟩ := hH T Tp ι π hT hTp c hc hext e ⟨hspan, hφe, hγe⟩
  have hext' := hext
  unfold Formalism.MainNotions.LiftingTheory.IsExtOf at hext'
  obtain ⟨hses, -⟩ := hext'
  have hinj : Function.Injective (W.map ι) := by
    have hs' := hses
    unfold Formalism.WeaklyAdmissibleFiltrations.IsSESLat at hs'
    obtain ⟨hιinj, -, honto, hex, hsat⟩ := hs'
    unfold Formalism.WeaklyAdmissibleFiltrations.LatHom.Onto at honto
    let ι' : ↥T.L.T →ₗ[O] ↥Tp.L.T := (ι.f.restrictScalars O).restrict ι.T_le
    let π' : ↥Tp.L.T →ₗ[O] ↥W.one.L.T := (π.f.restrictScalars O).restrict π.T_le
    have hπs : Function.Surjective π' := by
      rintro ⟨w, hw⟩
      obtain ⟨x0, hx0, hxw⟩ := honto w hw
      exact ⟨⟨x0, hx0⟩, Subtype.ext hxw⟩
    haveI : Module.Free O ↥W.one.L.T := W.one.L.free
    obtain ⟨s, hs⟩ := Module.projective_lifting_property π' LinearMap.id hπs
    let p0 : ↥Tp.L.T →ₗ[O] ↥Tp.L.T := LinearMap.id - s ∘ₗ π'
    have hrange : ∀ b : ↥Tp.L.T, p0 b ∈ LinearMap.range ι' := by
      intro b
      have h0 : π' (p0 b) = 0 := by
        rw [show p0 b = b - s (π' b) from rfl, map_sub,
          ← LinearMap.comp_apply π' s, hs, LinearMap.id_apply, sub_self]
      obtain ⟨y0, hy0⟩ := (hex _).1 (congrArg Subtype.val h0)
      have hyT : y0 ∈ T.L.T := hsat y0 (by rw [hy0]; exact (p0 b).2)
      exact ⟨⟨y0, hyT⟩, Subtype.ext hy0⟩
    have hι'inj : Function.Injective ι' := by
      intro a b hab
      exact Subtype.ext (hιinj (congrArg Subtype.val hab))
    let e := LinearEquiv.ofInjective ι' hι'inj
    let cr := p0.codRestrict (LinearMap.range ι') hrange
    let r : ↥Tp.L.T →ₗ[O] ↥T.L.T := e.symm.toLinearMap ∘ₗ cr
    have hr : ∀ a, r (ι' a) = a := by
      intro a
      have hπι : π' (ι' a) = 0 := by
        apply Subtype.ext
        show π.f (ι.f (a : T.V)) = 0
        exact (hex _).2 ⟨a, rfl⟩
      have hcr : cr (ι' a) = e a := by
        apply Subtype.ext
        simp only [cr, p0, LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply,
          LinearMap.comp_apply, hπι, map_zero, sub_zero, e, LinearEquiv.ofInjective_apply]
      change e.symm (cr (ι' a)) = a
      rw [hcr, e.symm_apply_apply]
    have hL : Function.LeftInverse (LinearMap.lTensor RW r) (LinearMap.lTensor RW ι') := by
      intro t0
      have h3 : r ∘ₗ ι' = LinearMap.id := LinearMap.ext hr
      have h4 := congrArg (fun f => f t0) (congrArg (LinearMap.lTensor RW) h3)
      simpa only [LinearMap.lTensor_comp, LinearMap.comp_apply, LinearMap.lTensor_id,
        LinearMap.id_apply] using h4
    intro x1 x2 h12
    apply E.jD_inj T
    apply hL.injective
    have h1 := E.jD_map ι x1
    have h2 := E.jD_map ι x2
    rw [h12] at h1
    exact h1.symm.trans h2
  have hx' : ((u⁻¹ : Oˣ) : O) • x ∈ W.N Tp := smulO_mem W Tp _ hx
  have hx'e : W.map π (((u⁻¹ : Oˣ) : O) • x) = (((u⁻¹ : Oˣ) : O) * ((PD.p : ℕ) : O) ^ k) • e := by
    rw [map_smulO, hxe, smul_smul]
  have hJ' : Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T Mi hi := fun τ i hτ => hJ i τ hτ
  unfold Formalism.MainNotions.DeltaInvariantLattices.WachMaxJumpBound at h8
  have h8' := h8 T Mi hi hT hJ'
  unfold Formalism.MainNotions.DeltaInvariantLattices.p8 at h8'
  obtain ⟨⟨y, hy, hy'⟩, ⟨z, hz, hz'⟩⟩ := h8' Tp ι π hses hTp e he hφe hγe _ hx' _ hx'e
  have hcoc : (y, z) ∈ W.divisibleCocycles T := by
    have h0 := pull_cocycle W ι hinj W.gam _ y z hy' hz'
    simp only [LocWach.divisibleCocycles, herrCocycles, LinearMap.mem_ker, LinearMap.coprod_apply, LinearMap.sub_apply,
      LinearMap.neg_apply, LinearMap.id_apply]
    rw [← sub_eq_add_neg]
    exact h0
  refine ⟨y, z, hcoc, ?_, ?_, ?_⟩
  · have hy2 : W.Q ^ Formalism.MainNotions.DeltaInvariantLattices.mx Mi • y ∈ W.N T := hy
    have hn : n ≠ 0 := by
      haveI := PD.finK₀
      rw [W.n_eq]
      exact Module.finrank_pos.ne'
    haveI : NeZero n := ⟨hn⟩
    have hle : Formalism.MainNotions.DeltaInvariantLattices.mx Mi ≤ Mmax n Mi := by
      unfold Formalism.MainNotions.DeltaInvariantLattices.mx Mmax
      apply ciSup_le
      intro i
      calc Mi i = Mi ((i.val : ℕ) : ZMod n) := by rw [ZMod.natCast_zmod_val]
        _ ≤ _ := Finset.le_sup (f := fun k : ℕ => Mi (k : ZMod n)) (Finset.mem_range.2 (ZMod.val_lt i))
    rw [← Nat.sub_add_cancel hle, pow_add, mul_smul]
    exact (W.N T).smul_mem _ hy2
  · obtain ⟨z', hz'N, hzz⟩ := hz
    exact ⟨z', hz'N, hzz.symm⟩
  · rw [hu _ _ hx'e y z hcoc hy' hz', ← mul_assoc, Units.mul_inv, one_mul]

theorem coreExtΔ_of (W : LocWach PD LL O v n)
    (E : EtTie W RA RW inclR φR gR πA)
    (hdex : W.DelF.card = PD.p - 1 → ∃ d : O, d * (W.DelF.card : O) = 1)
    (h8 : Formalism.MainNotions.DeltaInvariantLattices.WachMaxJumpBound W) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hH : Formalism.MainNotions.ElementDenominator.coreHerrExtΔ W) :
    coreExtΔ W := by
  have := liftb_neZero W
  intro hA T Tp ι π Mi hi cT cTp hJ c hc hExt k hImg
  have hs : W.s = 1 := hA.2.1
  have hp2 : PD.p ≠ 2 := hA.2.2
  have hK : W.gamK = W.gam := W.gamK_eq_one hs hp2
  have hcard : W.DelF.card = PD.p - 1 := by
    rw [(h9 T cT hs hp2).1, finrank_eq_one_case_A W hA, Nat.div_one]
  obtain ⟨d, hd⟩ := hdex hcard
  obtain ⟨e, he, hspan, hφe, hγe, x, hx, hxe⟩ := hImg
  have hses := hExt.1
  have hinj := linj_map_inj W E ι π hses
  obtain ⟨u, hu⟩ := hH hs hp2 T Tp ι π cT cTp c hc hExt e ⟨hspan, hφe, hγe⟩
  have hxb := lifta_avg_N W Tp d x hx
  have hmb : W.map π (lifta_avg W Tp d x) = ((PD.p : ℕ) : O) ^ k • e := by
    rw [lifta_avg_map, hxe]
    exact lifta_avg_fix W W.one d hd _ (fun δ _ => by rw [LinearMap.map_smul, hγe])
  have hx'N : ((u⁻¹ : Oˣ) : O) • lifta_avg W Tp d x ∈ W.NΔ Tp := (W.NΔ Tp).smul_mem _ hxb
  have hmap : W.map π (((u⁻¹ : Oˣ) : O) • lifta_avg W Tp d x) =
      (((u⁻¹ : Oˣ) : O) * ((PD.p : ℕ) : O) ^ k) • e := by
    rw [map_smulO, hmb, smul_smul]
  generalize ((u⁻¹ : Oˣ) : O) • lifta_avg W Tp d x = x' at hx'N hmap
  have h8T := h8 T Mi hi cT (liftb_jl W T Mi hi hJ)
  rw [liftb_mx_eq] at h8T
  obtain ⟨⟨y, hy, hyι⟩, ⟨z, hz, hzι⟩⟩ := h8T Tp ι π hses cTp e he hφe hγe x' hx'N.1 _ hmap
  have hzι' : W.map ι z = W.γD Tp W.gamK x' - x' := by rw [hK]; exact hzι
  have hyΔ : ∀ δ ∈ W.DelF, W.γD T δ y = y := fun δ hδ => by
    apply hinj
    rw [W.map_γ, hyι, map_sub, ← W.φγ_comm, hx'N.2 δ hδ]
  have hzΔ : ∀ δ ∈ W.DelF, W.γD T δ z = z := fun δ hδ => by
    apply hinj
    rw [W.map_γ, hzι', map_sub, ← W.γD_mul, mul_comm, W.γD_mul, hx'N.2 δ hδ]
  have hZ : (y, z) ∈ W.wachCocyclesDelta T := by
    rw [lifta_mem_Z1DΔ]
    refine ⟨?_, fun δ hδ => ⟨hyΔ δ hδ, hzΔ δ hδ⟩⟩
    rw [hK]
    exact (liftb_mem_Z1D W T y z).2 (pull_cocycle W ι hinj W.gam x' y z hyι hzι)
  obtain ⟨h9r, h9m⟩ := uniformizer_ring_and_module_clauses W h9 hA T cT
  refine ⟨y, z, hZ, ?_, ?_, ?_⟩
  · obtain ⟨w, hw⟩ := h9r.2.2.2.2.1
    rw [eisenstein_at_uniformizer] at hw
    have hyN : W.Q ^ Mmax n Mi • y ∈ W.N T := hy
    rw [lifta_Q_eq W hs, hw, mul_pow, mul_smul] at hyN
    have h2 := (W.N T).smul_mem (((w⁻¹ : (LetA O n)ˣ) : LetA O n) ^ Mmax n Mi) hyN
    rwa [smul_smul, ← mul_pow, Units.inv_mul, one_pow, one_smul] at h2
  · obtain ⟨z₁, hz₁, hzz⟩ := hz
    have hzN : z ∈ W.N T := by
      rw [← hzz]
      exact (W.N T).smul_mem _ hz₁
    exact lifta_interN W T h9r h9m z ⟨hzN, hzΔ⟩
      ⟨z₁, hz₁, by rw [← hzz, ← lifta_X_eq W hs]; rfl⟩
  · rw [hu x' _ hx'N.2 hmap y z hZ hyι hzι', ← mul_assoc, Units.mul_inv, one_mul]

end Core

end Formalism.MainNotions.UnusedSlot35.ExtCPf

namespace Formalism.MainNotions.UnusedSlot35

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem extension_clause (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) :
    Formalism.MainNotions.UnusedSlot35.ExtensionClassTheorem D HW F := by
  intro hadm
  obtain ⟨-, h8, hU⟩ := hadm
  intro l _ K s LL h
  exact ExtCPf.coreExt_of _ ((F l).E K s LL h).tie (h8 l K s LL h) (hU l K s LL h).1

theorem extension_invariant_clause (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) :
    Formalism.MainNotions.UnusedSlot35.InvariantCocycleClassTheorem D HW F := by
  intro hadm
  obtain ⟨-, h8, h9, -, hU⟩ := hadm
  intro l _ K s LL h
  refine ExtCPf.coreExtΔ_of _ ((F l).E K s LL h).tie ?_ (h8 l K s LL h) (h9 l K s LL h)
    (hU l K s LL h).2

  intro hc
  rw [hc, (D.loc l).PD_p K]
  have hl : 1 ≤ l := (Fact.out : l.Prime).one_le
  have hv : (D.loc l).v LL ((l : ↥LL.1) - 1) = 0 := by
    rw [sub_eq_add_neg, AddValuation.map_add_of_distinct_val, (D.loc l).v_l LL,
      AddValuation.map_neg, AddValuation.map_one]
    · exact min_eq_right zero_le_one
    · rw [(D.loc l).v_l LL, AddValuation.map_neg, AddValuation.map_one]
      exact one_ne_zero
  have hne : (l : ↥LL.1) - 1 ≠ 0 := by
    intro h0
    rw [h0, AddValuation.map_zero] at hv
    simp at hv
  have hvx : 0 ≤ (D.loc l).v LL ((l : ↥LL.1) - 1)⁻¹ := by
    simp only [AddValuation.map_inv, hv, neg_zero, le_refl]
  refine ⟨⟨((l : ↥LL.1) - 1)⁻¹, ((D.loc l).v_O LL _).1 hvx⟩, ?_⟩
  apply Subtype.ext
  simp [Nat.cast_sub hl, hne]

end Formalism.MainNotions.UnusedSlot35
