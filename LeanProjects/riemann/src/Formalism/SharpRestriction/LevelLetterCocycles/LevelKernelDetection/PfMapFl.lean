import Formalism.SharpRestriction.LevelLetterCocycles.FinalLevelsOf

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G Formalism.MainNotions.N.Ln03 TensorProduct

section General

variable {LL Qp : Type} [Field LL] [Field Qp] [Algebra Qp LL]
  {V₁ V₂ : Type} [AddCommGroup V₁] [Module LL V₁] [Module Qp V₁] [IsScalarTower Qp LL V₁]
  [AddCommGroup V₂] [Module LL V₂] [Module Qp V₂] [IsScalarTower Qp LL V₂]
  {B₁ B₂ : Type} [AddCommGroup B₁] [Module Qp B₁] [AddCommGroup B₂] [Module Qp B₂]

theorem pfMapFl_map_comm (f : V₁ →ₗ[LL] V₂) (g : B₁ →ₗ[Qp] B₂) (z : V₁ ⊗[Qp] B₁) :
    AlgebraTensorModule.map f (LinearMap.id : B₂ →ₗ[Qp] B₂)
        (AlgebraTensorModule.map (LinearMap.id : V₁ →ₗ[LL] V₁) g z) =
      AlgebraTensorModule.map (LinearMap.id : V₂ →ₗ[LL] V₂) g
        (AlgebraTensorModule.map f (LinearMap.id : B₁ →ₗ[Qp] B₁) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp
  | add x y hx hy => simp only [map_add, hx, hy]

end General

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W} {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}

section Filt

variable {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)

abbrev pfMapFl_Fb : T₁.V ⊗[Qp] B →ₗ[LL] T₂.V ⊗[Qp] B :=
  AlgebraTensorModule.map F.f (LinearMap.id : B →ₗ[Qp] B)

abbrev pfMapFl_FdR : T₁.V ⊗[Qp] BdR →ₗ[LL] T₂.V ⊗[Qp] BdR :=
  AlgebraTensorModule.map F.f (LinearMap.id : BdR →ₗ[Qp] BdR)

theorem pfMapFl_ιV (z : T₁.V ⊗[Qp] B) :
    ιV PD (LL := LL) (V := T₂.V) (pfMapFl_Fb F z) =
      pfMapFl_FdR F (ιV PD (LL := LL) (V := T₁.V) z) :=
  (pfMapFl_map_comm F.f (PD.ι.toLinearMap.restrictScalars Qp) z).symm

theorem pfMapFl_φ (z : T₁.V ⊗[Qp] B) :
    φVB PD (LL := LL) (V := T₂.V) (pfMapFl_Fb F z) =
      pfMapFl_Fb F (φVB PD (LL := LL) (V := T₁.V) z) :=
  (pfMapFl_map_comm F.f PD.φ.toLinearMap z).symm

theorem pfMapFl_φpow (s : ℕ) (z : T₁.V ⊗[Qp] B) :
    ((φVB PD (LL := LL) (V := T₂.V) : Module.End LL (T₂.V ⊗[Qp] B)) ^ s)
        (pfMapFl_Fb F z) =
      pfMapFl_Fb F (((φVB PD (LL := LL) (V := T₁.V) : Module.End LL (T₁.V ⊗[Qp] B)) ^ s) z) := by
  induction s generalizing z with
  | zero => rfl
  | succ s ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, pfMapFl_φ, ih]

theorem pfMapFl_act (g : G) (z : T₁.V ⊗[Qp] B) :
    actVB PD T₂.ρ g (pfMapFl_Fb F z) = pfMapFl_Fb F (actVB PD T₁.ρ g z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x b => simp [actVB, F.equiv]
  | add x y hx hy =>
    simp only [map_add]
    rw [hx, hy]

theorem pfMapFl_dcris (z : T₁.V ⊗[Qp] B) (hz : z ∈ Dcris PD T₁.ρ) :
    pfMapFl_Fb F z ∈ Dcris PD T₂.ρ := by
  simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero] at hz ⊢
  intro g
  rw [pfMapFl_act, hz g]

theorem pfMapFl_dcrisL (τ₀ : K₀ →ₐ[Qp] LL) (z : T₁.V ⊗[Qp] B) (hz : z ∈ DcrisL PD T₁.ρ τ₀) :
    pfMapFl_Fb F z ∈ DcrisL PD T₂.ρ τ₀ := by
  rw [DcrisL, Submodule.mem_inf] at hz ⊢
  refine ⟨pfMapFl_dcris F z hz.1, ?_⟩
  have h2 := hz.2
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero] at h2 ⊢
  intro c
  have h3 : mulVB (K₀ := K₀) (B := B) (V := T₂.V) (LL := LL) c (pfMapFl_Fb F z) =
      pfMapFl_Fb F (mulVB (K₀ := K₀) (B := B) (V := T₁.V) (LL := LL) c z) :=
    (pfMapFl_map_comm F.f (LinearMap.mulLeft Qp (algebraMap K₀ B c)) z).symm
  rw [h3, h2 c, map_smul]

theorem pfMapFl_filV (a : ℤ) (z : T₁.V ⊗[Qp] BdR) (hz : z ∈ FilV PD (LL := LL) (V := T₁.V) a) :
    pfMapFl_FdR F z ∈ FilV PD (LL := LL) (V := T₂.V) a := by
  obtain ⟨w, rfl⟩ := hz
  exact ⟨AlgebraTensorModule.map F.f LinearMap.id w,
    (pfMapFl_map_comm F.f ((PD.Fil a).restrictScalars Qp).subtype w).symm⟩

theorem pfMapFl_filCris (a : ℤ) (z : T₁.V ⊗[Qp] B) (hz : z ∈ FilCris PD T₁.ρ a) :
    pfMapFl_Fb F z ∈ FilCris PD T₂.ρ a := by
  rw [FilCris, Submodule.mem_inf, Submodule.mem_comap] at hz ⊢
  refine ⟨pfMapFl_dcris F z hz.1, ?_⟩
  rw [pfMapFl_ιV]
  exact pfMapFl_filV F a _ hz.2

theorem pfMapFl_filD {c : ZMod n} (h : MemD W F c) (s : ℕ) (u : ℤ) (x : Dc W T₁ c)
    (hx : x ∈ FilD W T₁ c s u) : dmapOf h x ∈ FilD W T₂ c s u := by
  have hx' : ιV PD (LL := LL) (V := T₁.V) (x : T₁.V ⊗[Qp] B) ∈ FilLev W T₁ c s u := hx
  obtain ⟨y', hy', hxy⟩ := Submodule.mem_map.1 hx'
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hy'
  show ιV PD (LL := LL) (V := T₂.V) (pfMapFl_Fb F (x : T₁.V ⊗[Qp] B)) ∈ FilLev W T₂ c s u
  refine Submodule.mem_map.2 ⟨_, Submodule.mem_map.2 ⟨pfMapFl_Fb F y,
    ⟨pfMapFl_filCris F u y hy.1, pfMapFl_dcrisL F _ y hy.2⟩, rfl⟩, ?_⟩
  rw [pfMapFl_φpow, pfMapFl_ιV, pfMapFl_ιV, hxy]

end Filt

section Xi

variable {T₁ T₂ : LocLat G Qp LL O} {F : LatHom T₁.L T₂.L} {c : ZMod n}

theorem pfMapFl_ambF_xi (h : MemD W F c) (s : ℕ) (x : Amb LL (KsW W s) (Dc W T₁ c))
    (hx : x ∈ Xi (KsW W s) (Tw (LL := LL) (D := Dc W T₁ c) 0)) :
    ambF h s x ∈ Xi (KsW W s) (Tw (LL := LL) (D := Dc W T₂ c) 0) := by
  have hx' : ∀ i, cf x i ∈ (Tw (LL := LL) (D := Dc W T₁ c) 0 i).baseChange (KsW W s) := hx
  show ∀ i, cf (ambF h s x) i ∈ (Tw (LL := LL) (D := Dc W T₂ c) 0 i).baseChange (KsW W s)
  intro i
  have hi := hx' i
  have hc : cf (ambF h s x) i = (dmapOf h).baseChange (KsW W s) (cf x i) := rfl
  rw [hc]
  unfold Tw at hi ⊢
  split_ifs at hi ⊢ with h0
  · rw [Submodule.baseChange_top]
    exact Submodule.mem_top
  · rw [Submodule.baseChange_bot, Submodule.mem_bot] at hi ⊢
    rw [hi, map_zero]

theorem pfMapFl_mem_FlS {hΔ : DeltaRho hR uZ ιZ c} {ell : ℕ} (Λ f' : PowerSeries O) (s : ℕ)
    (e : LvT hR uZ ιZ T₁ c hΔ ell) :
    e ∈ FlS (hR := hR) (uZ := uZ) (ιZ := ιZ) (T := T₁) (c := c) (hΔ := hΔ) (ell := ell) Λ f' s ↔
      ∃ x ∈ Xi (KsW W s) (Tw (LL := LL) (D := Dc W T₁ c) 0),
        prL s (Λ • e) = HahnSeries.ofPowerSeries ℤ (KsW W s) (rhoL hR c s f') • x := Iff.rfl

end Xi

section ThetaShiftProofs

variable {T₁ T₂ : LocLat G Qp LL O} {C₁ : Coord W (baseIdOf hR) T₁} {C₂ : Coord W (baseIdOf hR) T₂}
  {F : LatHom T₁.L T₂.L} {c : ZMod n} {ell : ℕ} {H : ℕ → ℕ} {κ₁ κ₂ : PowerSeries O} {r₁ r₂ : ℕ}
  {lam₁ : Fin r₁ → Dc W T₁ c} {lam₂ : Fin r₂ → Dc W T₂ c}

theorem mapFl_holds
    (Hy₁ : LvHyp Lb hR uZ ιZ C₁ c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) κ₁ lam₁)
    (Hy₂ : LvHyp Lb hR uZ ιZ C₂ c ell (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) κ₂ lam₂)
    (Mh : MapHyp hR uZ ιZ F c) (j M g η : ℕ) (kind : ℕ → Kind) (b : ℕ → ℕ) :
    ∀ s < ell, ∀ e ∈ (lvData Hy₁ ((baseIdOf hR).Bs.ff' ell j M g) kind b η).Fl s,
      prEOf Mh (hΔ₁ := Hy₁.delta) (hΔ₂ := Hy₂.delta) ell e ∈
        (lvData Hy₂ ((baseIdOf hR).Bs.ff' ell j M g) kind b η).Fl s := by
  intro s hs e he
  obtain ⟨x, hx, hex⟩ := (pfMapFl_mem_FlS (hΔ := Hy₁.delta)
    (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) ((baseIdOf hR).Bs.ff' ell j M g) s e).1 he
  refine (pfMapFl_mem_FlS (hΔ := Hy₂.delta)
    (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) ((baseIdOf hR).Bs.ff' ell j M g) s _).2
    ⟨ambF Mh.memD s x, pfMapFl_ambF_xi Mh.memD s x hx, ?_⟩
  have hsm := (prEOf Mh (hΔ₁ := Hy₁.delta) (hΔ₂ := Hy₂.delta) ell).map_smul
    (Formalism.ExponentWindows.abelian₂ (baseIdOf hR).Bs.p H ell) e
  erw [← hsm, prL_prEOf Mh s hs, hex, Mh.smul]

theorem cMap_holds (hD : MemD W F c) (kind : ℕ → Kind) (b : ℕ → ℕ) (η : ℕ)
    (P : (Fin r₁ → O) →ₗ[O] (Fin r₂ → O))
    (hLamP : ∀ k, dmapOf hD (lam₁ k) = ∑ l, algebraMap O LL (LinearMap.toMatrix' P l k) • lam₂ l) :
    ∀ s < ell, kind s = Kind.up → Formalism.ExponentWindows.E.CMap (UL lam₁ kind b η s) (UL lam₂ kind b η s) P := by
  intro s _ hk w hw
  have hw' : ∑ k, algebraMap O LL (w k) • lam₁ k ∈ FilD W T₁ c s ((b s : ℕ) : ℤ) := by
    have := hw
    simp only [UL, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_ofPred_eq,
      hk, UOf] at this
    exact this
  have hmap := pfMapFl_filD F hD s _ _ hw'
  have hsum : dmapOf hD (∑ k, algebraMap O LL (w k) • lam₁ k) =
      ∑ l, algebraMap O LL (P w l) • lam₂ l := by
    rw [map_sum]
    simp only [map_smul, hLamP, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.sum_smul, ← LinearMap.toMatrix'_mulVec P w]
    simp only [Matrix.mulVec, dotProduct, map_sum]
    refine congrArg (· • lam₂ l) (Finset.sum_congr rfl fun k _ => ?_)
    rw [map_mul]
    ring
  rw [hsum] at hmap
  show ∑ l, algebraMap O LL (P w l) • lam₂ l ∈ UOf (kind s) (b s) η (FilD W T₂ c s)
  rw [hk]
  exact hmap

end ThetaShiftProofs

end Formalism.MainNotions.N.Ln03.Pf
