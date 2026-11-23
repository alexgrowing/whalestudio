import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBcrisComparisonFrobeniusNaturalityStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisTensorIdentificationNaturalStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrobeniusPotentialCocycleClass
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameBreuilKisinDatumExists
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InclLSmulCoord
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.ExtClass

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  {t : Wq l a →ₐ[ℤ_[l]] O} {ϖ : PiSys l e}
  {ι κ μ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [Fintype μ] [DecidableEq μ]
  {T Tp U : LocLat (Gl l) ℚ_[l] K O} {f : LatHom T.L Tp.L} {g : LatHom Tp.L U.L}

omit [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsUltrametricDist K] [IsUnitBall O K] in

theorem map_injective (hfg : IsSESLat (Qp := ℚ_[l]) f g) (B : Type) [AddCommGroup B] [Module O B] :
    Function.Injective (TensorProduct.map (LinearMap.id : B →ₗ[O] B) ((f.f.restrictScalars O).restrict f.T_le)) := by
  obtain ⟨h1, -, h3, h4, h5⟩ := hfg
  have := U.L.free
  refine LinearMap.lTensor_injective_of_exact_of_flat ((g.f.restrictScalars O).restrict g.T_le) (fun z => ?_)
    ((f.f.restrictScalars O).restrict f.T_le) (fun x y h => Subtype.ext (h1 (congrArg Subtype.val h)))
    (fun z => ⟨fun h => ?_, ?_⟩) B
  · obtain ⟨x, hx, h⟩ := h3 z.1 z.2
    exact ⟨⟨x, hx⟩, Subtype.ext h⟩
  · obtain ⟨y, hy⟩ := (h4 z.1).1 (congrArg Subtype.val h)
    exact ⟨⟨y, h5 y (hy ▸ z.2)⟩, Subtype.ext hy⟩
  · rintro ⟨y, rfl⟩
    exact Subtype.ext ((h4 _).2 ⟨y.1, rfl⟩)

theorem exists_solution {P : PhiMod O K l e a ι} {Q : PhiMod O K l e a κ} {R : PhiMod O K l e a μ}
    {I : Ident t ϖ P T} {Ip : Ident t ϖ Q Tp} {Iu : Ident t ϖ R U} {F : GlobalTheory.BK.Hom P Q} {G : GlobalTheory.BK.Hom Q R}
    (hfg : IsSESLat (Qp := ℚ_[l]) f g) (hF : IsMapOf I Ip f F) (hG : IsMapOf Ip Iu g G) (u : ME R) (x : ↥U.L.T)
    (hux : toW t ϖ R u = Iu.ofT x) (k : ℕ) {x₂ : Vec K a κ} (hx₂ : x₂ ∈ Q.M) (hGx : G.app x₂ = k • u.1)
    (v : ↥Tp.L.T) (hv : g.f v = x.1) {y : Vec K a ι} (hy : y ∈ ME P) (hFy : F.app y = Q.phi x₂ - x₂) :
    ∃ m₀, phiW t ϖ P m₀ - m₀ = toW t ϖ P ⟨y, hy⟩ ∧
      homW t ϖ F m₀ = toW t ϖ Q ⟨x₂, mem_ME_of_mem_M hx₂⟩ - k • Ip.ofT v := by
  obtain ⟨m₁, hm₁⟩ := I.exists_phiW_sub (toW t ϖ P ⟨y, hy⟩)
  have hfixp : ∀ z, phiW t ϖ Q (Ip.ofT z) = Ip.ofT z := fun z =>
    mem_Treal.1 (by rw [← Ip.range_ofT]; exact ⟨z, rfl⟩)
  have hfix : ∀ z, phiW t ϖ P (I.ofT z) = I.ofT z := fun z =>
    mem_Treal.1 (by rw [← I.range_ofT]; exact ⟨z, rfl⟩)
  have h1 : phiW t ϖ Q (homW t ϖ F m₁) - homW t ϖ F m₁ =
      phiW t ϖ Q (toW t ϖ Q ⟨x₂, mem_ME_of_mem_M hx₂⟩) - toW t ϖ Q ⟨x₂, mem_ME_of_mem_M hx₂⟩ := by
    rw [← homW_phiW, ← map_sub, hm₁, homW_toW, ← toW_phi t ϖ Q hx₂, ← map_sub]
    exact congrArg _ (Subtype.ext hFy)
  have h2 : homW t ϖ F m₁ - (toW t ϖ Q ⟨x₂, mem_ME_of_mem_M hx₂⟩ - k • Ip.ofT v) ∈ LinearMap.range Ip.ofT := by
    rw [Ip.range_ofT, mem_Treal, map_sub, map_sub, map_nsmul, hfixp, sub_eq_iff_eq_add.1 h1]
    abel
  obtain ⟨z, hz⟩ := h2
  have h3 : homW t ϖ G (homW t ϖ F m₁) = 0 := by
    apply Iu.j.injective
    rw [hG, hF, map_zero]
    induction I.j m₁ using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul w s =>
      have h0 : ((g.f.restrictScalars O).restrict g.T_le) (((f.f.restrictScalars O).restrict f.T_le) s) = 0 :=
        Subtype.ext ((hfg.2.2.2.1 _).2 ⟨s.1, rfl⟩)
      simp only [latW, TensorProduct.map_tmul, h0, TensorProduct.tmul_zero]
    | add p q hp hq => simp only [map_add, hp, hq, add_zero]
  have h4 : homW t ϖ G (toW t ϖ Q ⟨x₂, mem_ME_of_mem_M hx₂⟩) = k • Iu.ofT x := by
    rw [homW_toW, ← hux, ← map_nsmul]
    exact congrArg _ (Subtype.ext hGx)
  have h5 : homW t ϖ G (Ip.ofT v) = Iu.ofT x := by
    rw [hG.homW_ofT]
    exact congrArg _ (Subtype.ext hv)
  have h6 := congrArg (homW t ϖ G) hz
  rw [map_sub, map_sub, map_nsmul, h3, h4, h5, sub_self, sub_self, hG.homW_ofT, ← map_zero Iu.ofT] at h6
  obtain ⟨s, hs⟩ := (hfg.2.2.2.1 z.1).1 (congrArg Subtype.val (Iu.ofT_injective h6))
  have hsT : s ∈ T.L.T := hfg.2.2.2.2 s (hs ▸ z.2)
  refine ⟨m₁ - I.ofT ⟨s, hsT⟩, ?_, ?_⟩
  · rw [map_sub, hfix, ← hm₁]
    abel
  · rw [map_sub, hF.homW_ofT, show (⟨f.f (⟨s, hsT⟩ : ↥T.L.T), f.T_le _ hsT⟩ : ↥Tp.L.T) = z from Subtype.ext hs, hz]
    abel

theorem isCrisVal_toW {P : PhiMod O K l e a ι} (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T) {w : Vec K a ι}
    (hL : w ∈ P.L) (hS : w ∈ P.MMl) :
    IsCrisVal t ϖ P jB (toW t ϖ P ⟨w, mem_ME_of_mem_L hL⟩) (jB (toBcris t ϖ P ⟨w, hS⟩)) := by
  refine ⟨1, fun i => ϖ.iTot t K (coordL P _ ⟨_, hL⟩ i), by rw [map_one]; exact isUnit_one, ?_, ?_⟩
  · rw [map_one, one_smul]
    exact (toW_toCris_of_mem_L t ϖ P hL (P.ext_mono (A_le_S l e) hL)).1
  · rw [map_one, one_smul]
    refine congrArg _ (funext fun i => ?_)
    rw [toBcris_apply, toB, AlgHom.comp_apply, ← ϖ.iC_of_mem t K, ← ϖ.iB_of_mem t K]
    rfl

variable [TameDescentExponentData K l e a] {η H : ℕ}

set_option maxHeartbeats 1600000 in

theorem classOf {D : BKDat O K l e a ι η H} {Dp : BKDat O K l e a κ η H} {Du : BKDat O K l e a μ η H}
    (R : GalDat t ϖ (sQ l) D T) (Rp : GalDat t ϖ (sQ l) Dp Tp) (Ru : GalDat t ϖ (sQ l) Du U)
    (F : BKHom D Dp) (G : BKHom Dp Du) (hfg : IsSESLat (Qp := ℚ_[l]) f g)
    (hF : IsMapOf R.I Rp.I f F.toHom) (hG : IsMapOf Rp.I Ru.I g G.toHom) (hinj : Function.Injective F.app)
    (u : ME Du.toPhiMod) (x : ↥U.L.T) (hux : toW t ϖ Du.toPhiMod u = Ru.I.ofT x) (n : ℕ) {x₂ : Vec K a κ}
    (hx₂ : x₂ ∈ Dp.Minv) (hGx : G.app x₂ = (l ^ n) • u.1) {v : Tp.V} {c : Gl l → T.V} (hv : v ∈ Tp.L.T)
    (hgv : g.f v = x.1) (hc : ∀ h, Tp.ρ h v - v = f.f (c h)) {σ : Vec K a ι} (hσ : σ ∈ D.MMl)
    (hσi : σ ∈ D.desc.inv) (hFσ : F.app σ = Dp.phi x₂ - Dp.xi (red (Dp.phi x₂))) {y : Vec K a ι} (hy : y ∈ D.Y)
    (hFy : F.app y = Dp.phi x₂ - x₂) : R.ClassOf y ((l : K) ^ n • c) := by
  have hyE : y ∈ ME D.toPhiMod := BKDat.mem_invE_of_mem_Y hy
  obtain ⟨m₀, hm₀, hFm₀⟩ := exists_solution hfg hF hG u x hux (l ^ n) hx₂.1 hGx ⟨v, hv⟩ hgv hyE hFy
  obtain ⟨b₀, hb₀⟩ := GlobalTheory.GalPot.exists_isCrisVal R hy hyE m₀ hm₀
  have hz : D.conn σ = D.zeta y := by
    apply hinj
    rw [F.toHom.app_conn, F.toHom.app_zeta, hFσ, hFy, PhiMod.zeta_phi_sub, map_sub, PhiMod.conn_xi, sub_zero]
  refine ⟨_, ⟨hyE, m₀, ⟨σ, hσ⟩, b₀, hm₀, hσi, hz, hb₀, rfl⟩, ?_⟩
  have hAS : A O K ≤ invL l (S O K e) := (A_le_S l e).trans (le_away _ _)
  have hL := Dp.phi_mem_L hx₂.1
  have hS : Dp.phi x₂ ∈ Dp.MMl := Dp.ext_mono hAS hL
  have hFS : F.app σ ∈ Dp.MMl := F.toHom.app_mem_ext hAS hσ
  have hξ : Dp.xi (red (Dp.phi x₂)) ∈ Dp.MMl := by
    have := sub_mem hS hFS
    rwa [hFσ, sub_sub_cancel] at this
  have hfixξ := GlobalTheory.GalPot.fix_of_horiz Rp ⟨_, hξ⟩ (fun γ => by
    change Dp.desc.act γ (Dp.xi _) = Dp.xi _
    rw [Descent.act_xi, ← Descent.red_act, Dp.desc.act_phi, hx₂.2 γ]) (Dp.conn_xi _)
  have N := GlobalTheory.T.bcrisTensorIdentification_natural l a e O K t ϖ ι D.toPhiMod T R.I R.jB R.cmp κ Dp.toPhiMod Tp Rp.I Rp.jB f
    F.toHom Rp.cmp hF
  have C := (GlobalTheory.T.breuilKisin_bcris_comparison_frobenius_naturality l a e O K t ϖ κ Dp.toPhiMod Tp Rp.I).2 Rp.jB Rp.cmp
  set Φ := TensorProduct.map (R := O) (LinearMap.id (R := O) (M := OB l O))
    ((f.f.restrictScalars O).restrict f.T_le) with hΦ
  have hfix : phiW t ϖ Dp.toPhiMod (Rp.I.ofT ⟨v, hv⟩) = Rp.I.ofT ⟨v, hv⟩ :=
    mem_Treal.1 (by rw [← Rp.I.range_ofT]; exact ⟨_, rfl⟩)
  have h1 := N.2 _ _ hb₀
  rw [homW_phiW, hFm₀, map_sub, map_nsmul, hfix, ← toW_phi t ϖ Dp.toPhiMod hx₂.1] at h1
  have h2 := C.2.1 _ _ _ h1 (IsCrisVal.sub t ϖ (isCrisVal_toW Rp.jB hL hS)
    (GlobalTheory.GalPot.isCrisVal_nsmul (C.2.2.2.1 ⟨v, hv⟩) (l ^ n)))
  have h3 : Φ (R.jB (toBcris t ϖ D.toPhiMod ⟨σ, hσ⟩) - b₀) =
      (l ^ n) • ((1 : OB l O) ⊗ₜ[O] (⟨v, hv⟩ : ↥Tp.L.T)) - Rp.jB (toBcris t ϖ Dp.toPhiMod ⟨_, hξ⟩) := by
    rw [map_sub, h2, ← N.1 ⟨σ, hσ⟩ ⟨_, hFS⟩ rfl,
      show (⟨F.app σ, hFS⟩ : Dp.MMl) = ⟨_, hS⟩ - ⟨_, hξ⟩ from Subtype.ext hFσ, map_sub, map_sub]
    abel
  intro γ k s hs
  apply map_injective hfg (OB l O)
  have hact : actB (sQ l) Tp γ ((1 : OB l O) ⊗ₜ[O] (⟨v, hv⟩ : ↥Tp.L.T)) =
      (1 : OB l O) ⊗ₜ[O] (Tp.actT γ ⟨v, hv⟩) := by
    rw [actB, TWact, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, map_one]
  have hs' : (f.f.restrictScalars O).restrict f.T_le s = (l : O) ^ k • (l : O) ^ n • (Tp.actT γ ⟨v, hv⟩ - ⟨v, hv⟩) := by
    have hsm : ∀ (j : ℕ) (w : Tp.V), ((l : O) ^ j) • w = (l : K) ^ j • w := fun j w => by
      rw [← algebraMap_smul K ((l : O) ^ j) w, map_pow, map_natCast]
    apply Subtype.ext
    change f.f (s : T.V) = (l : O) ^ k • (l : O) ^ n • (Tp.ρ γ v - v)
    rw [hs, hsm, hsm, hc, Pi.smul_apply, map_smul, map_smul]
  rw [map_smul, map_sub, GlobalTheory.CocycleNat.actB_map, ← hΦ, h3, map_sub, map_nsmul, hfixξ, hact, hΦ,
    TensorProduct.map_tmul, LinearMap.id_apply, hs', TensorProduct.tmul_smul, TensorProduct.tmul_smul,
    TensorProduct.tmul_sub, smul_sub, ← Nat.cast_smul_eq_nsmul O, ← Nat.cast_smul_eq_nsmul O, Nat.cast_pow]
  congr 1
  abel

set_option maxHeartbeats 1000000 in

theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (η H : ℕ) (T Tp : QLat LL) (f : LatHom T.L Tp.L) (g : LatHom Tp.L (unitLat (Gl l) : QLat LL).L), IsSESLat (Qp := ℚ_[l]) f g → ∀ (Pk : Pack a ϖ η H T) (Pp : Pack a ϖ η H Tp) (Pu : Pack a ϖ η H (unitLat (Gl l) : QLat LL)) (F : BKHom Pk.D Pp.D) (G : BKHom Pp.D Pu.D), IsMapOf Pk.R.I Pp.R.I f F.toHom → IsMapOf Pp.R.I Pu.R.I g G.toHom → IsExactTriple F.toHom G.toHom → Function.Injective F.app → ∀ (u : ME Pu.D.toPhiMod) (x : ↥(unitLat (Gl l) : QLat LL).L.T), x.1 = (1 : ↥LL.1) → u.1 ∈ Pu.D.Minv → Pu.D.phi u.1 = u.1 → toW (thetaW a LL) ϖ Pu.D.toPhiMod u = Pu.R.I.ofT x → ∀ (n : ℕ) (x₂ : Vec ↥LL.1 a (Fin Pp.n)), x₂ ∈ Pp.D.Minv → G.app x₂ = (l ^ n) • u.1 → ∀ (v : Tp.V) (c : Gl l → T.V), v ∈ Tp.L.T → g.f v = (1 : ↥LL.1) → (∀ h, Tp.ρ h v - v = f.f (c h)) → ∀ σ ∈ Pk.D.MMl, σ ∈ Pk.D.desc.inv → F.app σ = Pp.D.phi x₂ - Pp.D.xi (red (Pp.D.phi x₂)) → ∀ y ∈ Pk.D.Y, F.app y = Pp.D.phi x₂ - x₂ → Pk.R.ClassOf y ((l : ↥LL.1) ^ n • c) := by
  intro l _ a e _ _ ϖ LL _ _ η H T Tp f g hfg Pk Pp Pu F G hF hG _ hinj u x hx1 _ _ hux n x₂ hx₂ hGx₂ v c hv hgv hc σ hσ hσi hFσ y hy hFy
  exact classOf Pk.R Pp.R Pu.R F G hfg hF hG hinj u x hux n hx₂ hGx₂ hv (hgv.trans hx1.symm) hc hσ hσi hFσ hy hFy

end GlobalTheory.ExtClass
