import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ExDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Descend
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LocCondQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedOrigin
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

namespace UpperTheory.V.GradeZeroInterpolatingElement.SymplecticFrames

open Matrix

private theorem totDisc_quot {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) :
    TotallyDisconnectedSpace (G ⧸ N) := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_one]
  refine Set.eq_singleton_iff_unique_mem.2 ⟨mem_connectedComponent, fun y hy => ?_⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  by_contra hx
  have hx' : x ∉ N := fun h => hx ((QuotientGroup.eq_one_iff x).2 h)
  have ho : IsOpen {g : G | g * x ∉ N} := hN.isOpen_compl.preimage (continuous_mul_const x)
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ho (by simpa using hx')
  let V : Subgroup (G ⧸ N) := U.toSubgroup.map (QuotientGroup.mk' N)
  have hVo : IsOpen (V : Set (G ⧸ N)) := QuotientGroup.isOpenMap_coe _ U.isOpen'
  have hV : IsClopen (V : Set (G ⧸ N)) := ⟨V.isClosed_of_isOpen hVo, hVo⟩
  obtain ⟨u, hu, hux⟩ := hV.connectedComponent_subset V.one_mem hy
  exact hU (U.toSubgroup.inv_mem hu) (QuotientGroup.eq.1 hux)

section Form

variable {O R : Type} [CommRing O] [CommRing R] [Algebra O R]

private theorem JR_eq : (form O).JR R = J4 R := by
  show (J4 O).map (algebraMap O R) = J4 R
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J4]

private theorem J_adj (X : M4 R) : J4 R * adj X = Xᵀ * J4 R := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adj_apply, sgn, J4, Fin.rev, Matrix.mul_apply, Fin.sum_univ_four]

private theorem J_sq : -J4 R * J4 R = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J4, Matrix.mul_apply, Fin.sum_univ_four]

private theorem gsp_iff (ν : R) (X : M4 R) : IsGSp ν X ↔ Xᵀ * J4 R * X = ν • J4 R := by
  unfold IsGSp
  rw [← J_adj, mul_assoc]
  refine ⟨fun h => by rw [h, mul_smul_comm, mul_one], fun h => ?_⟩
  rw [← one_mul (adj X * X), ← J_sq, mul_assoc, h, mul_smul_comm]

private theorem gsp_diag (ν : R) (d : Fin 4 → R) (h : ∀ i, d i * d i.rev = ν) : IsGSp ν (diagonal d) := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  rw [gsp_iff]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [J4, Matrix.mul_diagonal, Matrix.diagonal_mul] <;> assumption

private theorem pres_iff {J X Y Y' : M4 R} {ν : R} (h1 : Y * Y' = 1) (h2 : Y' * Y = 1) (hY : Yᵀ * J * Y = ν • J) :
    (X * Y')ᵀ * J * (X * Y') = J ↔ Xᵀ * J * X = ν • J := by
  have h3 : Y'ᵀ * Yᵀ = 1 := by rw [← transpose_mul, h1, transpose_one]
  have h4 : Yᵀ * Y'ᵀ = 1 := by rw [← transpose_mul, h2, transpose_one]
  have e : (X * Y')ᵀ * J * (X * Y') = Y'ᵀ * (Xᵀ * J * X) * Y' := by
    simp only [transpose_mul, mul_assoc]
  rw [e, ← hY]
  constructor
  · intro h
    calc Xᵀ * J * X = (Yᵀ * Y'ᵀ) * (Xᵀ * J * X) * (Y' * Y) := by rw [h4, h2, one_mul, mul_one]
      _ = Yᵀ * (Y'ᵀ * (Xᵀ * J * X) * Y') * Y := by simp only [mul_assoc]
      _ = _ := by rw [h]
  · intro h
    rw [h]
    calc Y'ᵀ * (Yᵀ * J * Y) * Y' = (Y'ᵀ * Yᵀ) * J * (Y * Y') := by simp only [mul_assoc]
      _ = J := by rw [h3, h1, one_mul, mul_one]

private theorem hh_iff [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [IsCO O R]
    {Γ : Type} [Group Γ] [TopologicalSpace Γ] {rb : Γ →* M4 (ResidueField O)} (r0 : Lift O rb O) (r : Lift O rb R)
    (s : Γ) (ν : O) (h : IsGSp ν (r0.hom s)) :
    (form O).HH (r.hom s * (r0.hom s⁻¹).map (algebraMap O R)) ↔ IsGSp (algebraMap O R ν) (r.hom s) := by
  have h1 : (r0.hom s).map (algebraMap O R) * (r0.hom s⁻¹).map (algebraMap O R) = 1 := by
    rw [← Matrix.map_mul, ← map_mul, mul_inv_cancel, map_one, Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 : (r0.hom s⁻¹).map (algebraMap O R) * (r0.hom s).map (algebraMap O R) = 1 := by
    rw [← Matrix.map_mul, ← map_mul, inv_mul_cancel, map_one, Matrix.map_one _ (map_zero _) (map_one _)]
  have h3 : ((r0.hom s).map (algebraMap O R))ᵀ * J4 R * (r0.hom s).map (algebraMap O R) = algebraMap O R ν • J4 R := by
    rw [gsp_iff] at h
    have e : J4 R = (J4 O).map (algebraMap O R) := (JR_eq (O := O)).symm
    rw [e, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, h]
    ext i j
    simp
  have h4 : (r.hom s * (r0.hom s⁻¹).map (algebraMap O R)).map (res O R) = 1 := by
    have e1 : (r.hom s).map (res O R) = rb s := Matrix.ext fun a b => r.red s a b
    have e2 : ((r0.hom s⁻¹).map (algebraMap O R)).map (res O R) = rb s⁻¹ := Matrix.ext fun a b => by
      rw [← r0.red s⁻¹ a b]
      exact res_map (Algebra.ofId O R) _
    rw [Matrix.map_mul, e1, e2, ← map_mul, mul_inv_cancel, map_one]
  rw [gsp_iff, ← pres_iff h1 h2 h3]
  unfold FormData.HH
  rw [JR_eq]
  exact ⟨fun h => h.1, fun h => ⟨h, fun a b hab => absurd rfl hab, h4⟩⟩

private theorem hh_sp [IsLocalRing O] [IsCO O R] (h : M4 R) : (form O).HH h ↔ Sp1 O h := by
  unfold FormData.HH Sp1
  rw [JR_eq, gsp_iff, one_smul]
  exact ⟨fun k => ⟨k.1, k.2.2⟩, fun k => ⟨k.1, fun a b hab => absurd rfl hab, k.2⟩⟩

private theorem z_mem_max {X : Type} [AddCommGroup X] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] [IsCO O R] (W : WPres O X R) (h : W.HasOrigin) (s : W.σ) :
    W.z s ∈ maximalIdeal R := by
  rw [← res_eq_zero_iff O, ← res_map (W.origin h), WPres.z, W.origin_π, MvPowerSeries.constantCoeff_X, map_zero]

end Form

end UpperTheory.V.GradeZeroInterpolatingElement.SymplecticFrames

open UpperTheory.V.GradeZeroInterpolatingElement.SymplecticFrames in
theorem UpperTheory.nonempty_local_frames_of_good_data :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → LemmaP → PhiCond D.Gam l → D.Nums → ∀ L : LocBase D, Nonempty (Fr D L) := by
  intro Ω _ _ _ l hl c D hD hP hΦ hN L
  obtain ⟨rb, r0, hb, h0, nb, n0, H⟩ := descend D hD
  obtain ⟨-, -, f3, -, -, hrev, -⟩ := facts D hD
  obtain ⟨-, hfin, hlm, -⟩ := abelian₂.dvr_finite l c.O
  haveI : CharP (ResidueField c.O) l := (CharP.charP_iff_prime_eq_zero hl.out).2 (by
    rw [← map_natCast (residue c.O), residue_eq_zero_iff]; exact hlm)
  have h2 : IsUnit (2 : c.O) := by
    obtain ⟨-, -, -, -, -, -, -, -, h⟩ := dvrFacts l c.O
    exact_mod_cast h 2 fun hd => hD.l_odd ((Nat.prime_dvd_prime_iff_eq hl.out Nat.prime_two).1 hd)
  haveI : IsGalois ℚ Ω := {}
  haveI hcl := isClosed_NS Ω D.SP
  haveI : CompactSpace D.Gam := inferInstance
  haveI : T2Space D.Gam := inferInstance
  haveI : TotallyDisconnectedSpace D.Gam := totDisc_quot _ hcl
  have hs : Function.Surjective (toGS Ω D.SP) := QuotientGroup.mk_surjective
  have hb' : ∀ g, rb (toGS Ω D.SP g) = D.rbar g := fun g => DFunLike.congr_fun hb g
  have h0' : ∀ g, r0.hom (toGS Ω D.SP g) = D.r0 g := fun g => DFunLike.congr_fun h0 g
  have hd : ∀ g i, (D.ps i g : c.O) * (D.ps i.rev g : c.O) = D.th g := fun g i => by
    rw [← Units.val_mul, ← hrev i]
    rfl
  let ρ : ∀ v : D.frame.T, Lift c.O (rb.comp (D.frame.φ v)) L.B := fun v =>
    ⟨(L.ρ v).hom, (L.ρ v).cont, fun g a b => ((L.ρ v).red g a b).trans (congrFun (congrFun (hb' g.1) a) b).symm⟩
  let Lq : ∀ q : D.frame.Q, Cond c.O (rb.comp (D.frame.ψ q)) := fun q =>
    killCond (rb.comp (D.frame.ψ q)) (D.frame.N q)
  have hNq : ∀ q, ∀ n ∈ D.frame.N q, rb (D.frame.ψ q n) = 1 := fun q n hn => (hb' n.1).trans hn.2
  have hLq : ∀ q, (form c.O).IsLocCond (r0.hom.comp (D.frame.ψ q)) (D.frame.N q) (Lq q) := locCondQ D hD rb r0 hb h0
  have hL0 : ∀ q, Lq q c.O (r0.comap (D.frame.ψ q) (D.frame.hψ q)) := by
    obtain ⟨ρ0, e0, -, k⟩ := (H c.O).1 r0
    refine k.2 fun A hA g hg h1 => ?_
    rw [e0, h0]
    have : ∀ i, D.ps i g = 1 := fun i => f3 i A hA g hg h1
    show Matrix.diagonal (fun i => (D.ps i g : c.O)) = 1
    simp only [this, Units.val_one, Matrix.diagonal_one]
  have hmul : ∀ (v : D.T) (g : D.Gp v), IsGSp (algebraMap c.O L.B (D.th g)) ((L.ρ v).hom g) := by
    rintro ⟨v, hv⟩
    rcases Finset.mem_insert.1 hv with rfl | h
    · exact L.eqs.1.1
    · exact (L.eqs.2 v h).1
  have hIn : ∀ v, (form c.O).InH (r0.hom.comp (D.frame.φ v)) L.B (ρ v) := fun v s =>
    (hh_iff (r0.comap (D.frame.φ v) (D.frame.hφ v)) (ρ v) s (D.th s.1)
      (by
        have e : (r0.comap (D.frame.φ v) (D.frame.hφ v)).hom s = D.r0 s.1 := h0' s.1
        rw [e]
        exact gsp_diag _ _ (hd s.1))).2 (hmul v s)
  obtain ⟨R, _, _, _, i, r, α, W, τ, κ, _, _, e, f, wf, hU, hrel, k1, k2, k3, k4, k5⟩ :=
    hP l c.O hD.l_odd (Fin 4) (ℤ × ℤ) w4 (form c.O) D.Gam hΦ rb r0 nb n0 D.frame Lq hNq hLq hL0
      (fun j => (hN rb hb nb j).1) L.B L.W ρ (z_mem_max L.W L.org) hIn (fun v s a b => L.hom v s a b)
  obtain ⟨org, o1, o2, o3⟩ := framed_origin c.O (Fin 4) (ℤ × ℤ) w4 (form c.O) h2 D.Gam rb r0 nb n0 D.frame Lq hNq hLq hL0
    L.B ρ hIn L.W L.org (fun v s a b => (L.at0 v s a b).trans (congrFun (congrFun (h0' s.1) a) b).symm)
    R i r α hU W τ e (fun s => by
      have := hrel.2.1 (MvPowerSeries.X s)
      rw [MvPowerSeries.rename_X] at this
      exact this)
    (fun t => by
      obtain ⟨a, b, -, h⟩ := k3 t
      exact ⟨a, b, h⟩)
  have key : ∀ (R' : Type) [CommRing R'] [Algebra c.O R'] [IsCO c.O R'] (i' : L.B →ₐ[c.O] R') (s : Lift c.O rb R')
      (s' : Lift c.O D.rbar R') (α' : D.T → M4 R'), s'.hom = s.hom.comp (toGS Ω D.SP) →
      (IsFramed (form c.O) r0.hom D.frame Lq ρ i' s α' ↔ IsFr L i' s' α') := by
    intro R' _ _ _ i' s s' α' hss
    obtain ⟨s'', e'', m1, m2⟩ := (H R').1 s
    obtain rfl : s'' = s' := Lift.ext (e''.trans hss.symm)
    have hg : ∀ g, s''.hom g = s.hom (toGS Ω D.SP g) := fun g => DFunLike.congr_fun e'' g
    exact ⟨fun ⟨a1, a2, a3, a4, a5⟩ => ⟨m1.1 a1, m2.1 a2, fun v => (hh_sp _).1 (a3 v), a4,
        fun v g => by rw [hg]; exact a5 v g⟩,
      fun a => ⟨m1.2 a.mult, m2.2 a.unr, fun v => (hh_sp _).2 (a.sp v), a.atL,
        fun v g => by have := a.loc v g; rw [hg] at this; exact this⟩⟩
  obtain ⟨ru, eu, -⟩ := (H R).1 r
  have hg : ∀ g, ru.hom g = r.hom (toGS Ω D.SP g) := fun g => DFunLike.congr_fun eu g
  refine ⟨{ U := R, i := i, r := ru, α := α, fr := (key R i r ru α eu).1 hU.1, univ := ?_, W := W, τ := τ, κ := κ, e := e
            f := f, wf := wf, rel := hrel, homr := fun g a b => ?_, homα := k2, vars := fun t => ?_, org := org
            at0r := fun g a b => ?_, at0α := o2, at0i := o3, numf := fun j => ?_, numz := fun j j1 j2 j3 => ?_ }⟩
  · intro R' _ _ _ i' r' α' hF
    obtain ⟨s, es⟩ := (H R').2 r' hF.unr
    have hs' : ∀ g, r'.hom g = s.hom (toGS Ω D.SP g) := fun g => DFunLike.congr_fun es g
    have hiff : ∀ y : R →ₐ[c.O] R', r.map y = s ↔ ru.map y = r' := fun y => by
      constructor
      · intro h
        refine Lift.ext (MonoidHom.ext fun g => Matrix.ext fun a b => ?_)
        rw [Lift.map_hom, hg, hs', ← h, Lift.map_hom]
      · intro h
        refine Lift.ext (MonoidHom.ext fun g => Matrix.ext fun a b => ?_)
        obtain ⟨g, rfl⟩ := hs g
        rw [Lift.map_hom, ← hg, ← hs', ← h, Lift.map_hom]
    have := hU.2 R' i' s α' ((key R' i' s r' α' es).2 hF)
    simp only [hiff] at this
    exact this
  · rw [hg]; exact k1 _ a b
  · obtain ⟨a, b, h1, h⟩ := k3 t
    refine ⟨a, b, h1, h.imp_left ?_⟩
    rintro ⟨s, h⟩
    obtain ⟨g, rfl⟩ := hs s
    exact ⟨g, by rw [hg, ← h0']; exact h⟩
  · rw [hg, ← h0', ← o1, Lift.map_hom]
  · rw [k4, k5]; exact (hN rb hb nb j).2.1
  · rw [k4]; exact (hN rb hb nb j).2.2 j1 j2 j3
