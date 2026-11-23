import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormGeometrySummary
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagFramesSameGradedDefinitePartLatticeEq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EqCHolds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.EquivFramesSameSecondLatticeFiberProofStatement
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.FibreCountOfPositions

noncomputable section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals

namespace GlobalTheory.TypeAsm.InjProof
open Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat

section Core
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}

theorem X_map {F G : FlagD H r} (g : V ≃ₗ[K] V) (hG : ∀ c, G.e c = g (F.e c)) :
    G.X = F.X.map (g : V →ₗ[K] V) := by
  unfold FlagD.X FlagD.Xa
  rw [Submodule.map_span, Set.image_image]
  congr 1
  ext x; simp [hG]

theorem fix_X {F : FlagD H r} (a : V →ₗ[K] V) (ha : ∀ c, a (F.e c) = F.e c) {x : V} (hx : x ∈ F.X) :
    a x = x := by
  unfold FlagD.X FlagD.Xa at hx
  induction hx using Submodule.span_induction with
  | mem y hy => obtain ⟨b, -, rfl⟩ := hy; exact ha _
  | zero => simp
  | add y z _ _ h1 h2 => rw [map_add, h1, h2]
  | smul c y _ h1 => rw [map_smul, h1]

theorem B_sw {x y : V} (h : H.B x y = 0) : H.B y x = 0 := by
  rw [← H.herm, h, star_zero]

theorem isotropicSpan_first_le_framePairSpace {F G : FlagD H r} {x : V} (hx : x ∈ F.X) : x ∈ V0 F G :=
  Submodule.mem_sup_left (Submodule.mem_sup_left hx)

theorem isotropicSpan_second_le_framePairSpace {F G : FlagD H r} {x : V} (hx : x ∈ G.X) : x ∈ V0 F G :=
  Submodule.mem_sup_left (Submodule.mem_sup_right hx)

theorem lastVector_first_mem_framePairSpace (F G : FlagD H r) : F.z ∈ V0 F G :=
  Submodule.mem_sup_right (Submodule.subset_span (by simp))

theorem lastVector_second_mem_framePairSpace (F G : FlagD H r) : G.z ∈ V0 F G :=
  Submodule.mem_sup_right (Submodule.subset_span (by simp))

theorem core (F G₁ G₂ : FlagD H r) (γ n n' a : V ≃ₗ[K] V)
    (hG₁ : ∀ c, G₁.e c = γ (F.e c)) (hG₂ : ∀ c, G₂.e c = n (γ (a (n' (F.e c)))))
    (hn : ∀ x y, H.B (n x) (n y) = H.B x y)
    (hnX : ∀ x ∈ F.X, n x ∈ F.X) (hnP : ∀ x, (∀ b : Fin r, H.B (F.e b.castSucc) x = 0) → n x - x ∈ F.X)
    (hnsX : ∀ x ∈ F.X, n.symm x ∈ F.X)
    (hnsP : ∀ x, (∀ b : Fin r, H.B (F.e b.castSucc) x = 0) → n.symm x - x ∈ F.X)
    (hn'X : ∀ x ∈ F.X, n' x ∈ F.X) (hn'P : ∀ x, (∀ b : Fin r, H.B (F.e b.castSucc) x = 0) → n' x - x ∈ F.X)
    (hn'sX : ∀ x ∈ F.X, n'.symm x ∈ F.X)
    (ha : ∀ c, a (F.e c) = F.e c)
    (hI : ∀ x ∈ F.X, (∀ v ∈ V0 F G₁, H.B v x = 0) → x ∈ G₁.X)
    {v p y₁ y₂ : V} (hv : ∀ c, H.B (F.e c) v = 0) (hp : ∀ c, H.B (F.e c) p = 0)
    (hy₁ : y₁ ∈ wSp F G₁) (hy₁p : y₁ - p ∈ F.X) (hy₁v : y₁ - γ v ∈ G₁.X)
    (hy₂ : y₂ ∈ wSp F G₂) (hy₂p : y₂ - p ∈ F.X) (hy₂v : y₂ - n (γ (a (n' v))) ∈ G₂.X) :
    a v - v ∈ F.X := by
  set g₂ : V ≃ₗ[K] V := ((n'.trans a).trans γ).trans n with hg₂
  have hg₂a : ∀ x, g₂ x = n (γ (a (n' x))) := fun x => rfl
  have hX₁ : G₁.X = F.X.map (γ : V →ₗ[K] V) := X_map γ hG₁
  have hX₂ : G₂.X = F.X.map (g₂ : V →ₗ[K] V) := X_map g₂ (fun c => by rw [hg₂a]; exact hG₂ c)
  have hafX : ∀ x ∈ F.X, a x = x := fun x hx => fix_X (a : V →ₗ[K] V) ha hx

  have hnγX : ∀ x ∈ F.X, n (γ x) ∈ G₂.X := by
    intro x hx
    rw [hX₂]
    refine Submodule.mem_map.2 ⟨n'.symm x, hn'sX x hx, ?_⟩
    change g₂ (n'.symm x) = n (γ x)
    rw [hg₂a, LinearEquiv.apply_symm_apply, hafX x hx]
  have hzP : ∀ b : Fin r, H.B (F.e b.castSucc) F.z = 0 := fun b => F.zperp b
  have hnV0 : ∀ u ∈ V0 F G₁, n u ∈ V0 F G₂ := by
    intro u hu
    have hle : V0 F G₁ ≤ (V0 F G₂).comap (n : V →ₗ[K] V) := by
      refine sup_le (sup_le ?_ ?_) (Submodule.span_le.2 ?_)
      · intro x hx; exact isotropicSpan_first_le_framePairSpace (hnX x hx)
      · intro x hx
        rw [hX₁] at hx
        obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hx
        exact isotropicSpan_second_le_framePairSpace (hnγX y hy)
      · rintro x (rfl | rfl)
        · change n F.z ∈ V0 F G₂
          have : n F.z = F.z + (n F.z - F.z) := by abel
          rw [this]
          exact Submodule.add_mem _ (lastVector_first_mem_framePairSpace F G₂) (isotropicSpan_first_le_framePairSpace (hnP _ hzP))
        · change n (G₁.z) ∈ V0 F G₂
          have hx0 : n' F.z - F.z ∈ F.X := hn'P _ hzP
          have hz2 : G₂.z = n (γ F.z) + n (γ (n' F.z - F.z)) := by
            rw [FlagD.z, hG₂, ← map_add, ← map_add]
            congr 2
            have : n' (F.e (Fin.last r)) = F.z + (n' F.z - F.z) := by rw [FlagD.z]; abel
            rw [this, map_add, hafX _ hx0]
            have : a F.z = F.z := ha (Fin.last r)
            rw [this]
          have h1 : G₁.z = γ F.z := hG₁ (Fin.last r)
          rw [h1]
          have : n (γ F.z) = G₂.z - n (γ (n' F.z - F.z)) := by rw [hz2]; abel
          rw [this]
          exact Submodule.sub_mem _ (lastVector_second_mem_framePairSpace F G₂) (isotropicSpan_second_le_framePairSpace (hnγX _ hx0))
    exact hle hu

  rw [hX₁] at hy₁v
  obtain ⟨x₁, hx₁, hx₁e⟩ := Submodule.mem_map.1 hy₁v
  rw [hX₂] at hy₂v
  obtain ⟨x₂, hx₂, hx₂e⟩ := Submodule.mem_map.1 hy₂v
  have hvP : ∀ b : Fin r, H.B (F.e b.castSucc) v = 0 := fun b => hv _
  have hx'' : n' v - v + n' x₂ ∈ F.X := Submodule.add_mem _ (hn'P v hvP) (hn'X x₂ hx₂)
  have hy₂' : n.symm y₂ = γ (a v + (n' v - v + n' x₂)) := by
    have e1 : y₂ = g₂ (v + x₂) := by
      rw [map_add]; change y₂ = n (γ (a (n' v))) + g₂ x₂
      rw [show g₂ x₂ = (g₂ : V →ₗ[K] V) x₂ from rfl, hx₂e]; abel
    rw [e1, hg₂a, LinearEquiv.symm_apply_apply]
    congr 1
    have e2 : n' (v + x₂) = v + (n' v - v + n' x₂) := by rw [map_add]; abel
    rw [e2, map_add, hafX _ hx'']
  have hy₁' : y₁ = γ (v + x₁) := by
    rw [map_add]; change y₁ = γ v + (γ : V →ₗ[K] V) x₁
    rw [hx₁e]; abel

  set d := y₁ - n.symm y₂ with hd
  have hdX : d ∈ F.X := by
    have e : d = (y₁ - p) - n.symm (y₂ - p) - (n.symm p - p) := by rw [hd, map_sub]; abel
    rw [e]
    exact Submodule.sub_mem _ (Submodule.sub_mem _ hy₁p (hnsX _ hy₂p)) (hnsP p (fun b => hp _))
  have hdP : ∀ u ∈ V0 F G₁, H.B u d = 0 := by
    intro u hu
    have h1 : H.B u y₁ = 0 := B_sw ((mem_perp_iff H _ _).1 hy₁ u hu)
    have h2 : H.B u (n.symm y₂) = 0 := by
      have := hn u (n.symm y₂)
      rw [LinearEquiv.apply_symm_apply] at this
      rw [← this]
      exact B_sw ((mem_perp_iff H _ _).1 hy₂ _ (hnV0 u hu))
    rw [hd, map_sub, h1, h2, sub_zero]
  have hdG := hI d hdX hdP
  rw [hX₁] at hdG
  obtain ⟨x₃, hx₃, hx₃e⟩ := Submodule.mem_map.1 hdG
  have e3 : γ x₃ = γ (v + x₁ - (a v + (n' v - v + n' x₂))) := by
    change (γ : V →ₗ[K] V) x₃ = _
    rw [hx₃e, hd, hy₂', hy₁', map_sub]
  have e4 := γ.injective e3
  have e5 : a v - v = x₁ - (n' v - v + n' x₂) - x₃ := by rw [e4]; abel
  rw [e5]
  exact Submodule.sub_mem _ (Submodule.sub_mem _ hx₁ hx'') hx₃

end Core
end GlobalTheory.TypeAsm.InjProof

namespace GlobalTheory.TypeAsm.InjProof
open Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat
attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Obj
variable {D : D7} {X : HidaSetting D}

theorem fixedFrameOfWord_isotropicSpan_eq (u : D.what₂.Word) : (F0 X u).X = Xsp (lf D (X.Fu u)) := by
  show (frF (lf D (X.Fu u)).fl (tu_ne D u)).X = (lf D (X.Fu u)).fl.X
  unfold Formalism.HermitianLatticeCounting.S6.FlagD.X Formalism.HermitianLatticeCounting.S6.FlagD.Xa FlagG.X
  have h : (fun b : Fin D.R.rS => (frF (lf D (X.Fu u)).fl (tu_ne D u)).e b.castSucc) = (lf D (X.Fu u)).fl.e :=
    funext fun b => fv_cast _ b
  rw [h]
  congr 1
  ext x; simp

theorem Ft_e' {Y : Full X} {u : D.what₂.Word} (t : GT Y u) (a : Fin (D.R.rS + 1)) :
    (Ft t).e a = t.lin ((F0 X u).e a) := by
  have hi : t.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := t.rep.2.2.1
  show (mapLF t.lin (lf D (X.Fu u))).fl.fvec a = t.lin ((lf D (X.Fu u)).fl.fvec a)
  unfold mapLF
  simp only [dif_pos hi]
  refine Fin.lastCases ?_ (fun i => ?_) a
  · simp only [FlagG.fvec, Fin.snoc_last, mapFlag]
  · simp only [FlagG.fvec, Fin.snoc_castSucc, mapFlag]

theorem orth_of (u : D.what₂.Word) {x : (VS D).V} (h : ∀ b : Fin D.R.rS, (HV D).B ((F0 X u).e b.castSucc) x = 0) :
    x ∈ orth (VS D) (Xsp (lf D (X.Fu u))) := by
  rw [Formalism.MainNotions.BridgeLemma₂.c3eqv_mem_orth]
  intro v hv
  rw [← fixedFrameOfWord_isotropicSpan_eq] at hv
  unfold Formalism.HermitianLatticeCounting.S6.FlagD.X Formalism.HermitianLatticeCounting.S6.FlagD.Xa at hv
  induction hv using Submodule.span_induction with
  | mem y hy => obtain ⟨b, -, rfl⟩ := hy; exact p_symm_zero (VS D) (h b)
  | zero => simp
  | add y z _ _ h1 h2 => simp [map_add, h1, h2]
  | smul c y _ h1 => simp [h1]

theorem of_orth (u : D.what₂.Word) {x : (VS D).V} (h : x ∈ orth (VS D) (Xsp (lf D (X.Fu u)))) :
    ∀ b : Fin D.R.rS, (HV D).B ((F0 X u).e b.castSucc) x = 0 := by
  intro b
  rw [Formalism.MainNotions.BridgeLemma₂.c3eqv_mem_orth] at h
  have hb : (F0 X u).e b.castSucc ∈ Xsp (lf D (X.Fu u)) := by
    rw [← fixedFrameOfWord_isotropicSpan_eq]; exact Submodule.subset_span ⟨b, b.2, rfl⟩
  exact p_symm_zero (VS D) (h _ hb)

end Obj
end GlobalTheory.TypeAsm.InjProof

namespace GlobalTheory.TypeAsm.InjProof
open Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem injC : InjC := by
  intro D large₂ X Y u hStd W HW hEmb t₁ t₂ hN hlam hEqv h hH₁ hH₂
  obtain ⟨N, hd, hS, hS'⟩ := hN
  obtain ⟨hEq', n, a, hnL, ha_isom, ha_gmap, ha_fix, n', hn'L, hlin⟩ := GlobalTheory.T.equivFramesSameSecondLatticeFiber_proof D large₂ X Y u hStd t₁ t₂ hlam hEqv
  have hXF := fixedFrameOfWord_isotropicSpan_eq (X := X) u

  have hI : ∀ x ∈ (F0 X u).X, (∀ v ∈ V0 (F0 X u) (Ft t₁), (HV D).B v x = 0) → x ∈ (Ft t₁).X := by
    intro x hx hperp
    have hfull := (GlobalTheory.DegCnt.NFGeom.full N).2.2.2.2.2.1
    rw [GlobalTheory.DegAsm.AdaptInv.x_eq hS] at hfull
    rw [GlobalTheory.DegAsm.AdaptInv.sitesCommonSpace_v0_eq_Vp hS hS'] at hfull
    have := ((hfull x hx).1 hperp).2
    rwa [GlobalTheory.DegAsm.AdaptInv.x_eq hS'] at this
  have hnX : ∀ x ∈ (F0 X u).X, n x ∈ (F0 X u).X := by
    rw [hXF]; exact Formalism.MainNotions.BridgeLemma₂.c3eqv_N_X hnL
  have hnsX : ∀ x ∈ (F0 X u).X, n.symm x ∈ (F0 X u).X := by
    rw [hXF]; exact Formalism.MainNotions.BridgeLemma₂.c3eqv_N_X (Formalism.MainNotions.BridgeLemma₂.c3eqv_NLam_symm hnL)
  have hn'X : ∀ x ∈ (F0 X u).X, n' x ∈ (F0 X u).X := by
    rw [hXF]; exact Formalism.MainNotions.BridgeLemma₂.c3eqv_N_X hn'L
  have hn'sX : ∀ x ∈ (F0 X u).X, n'.symm x ∈ (F0 X u).X := by
    rw [hXF]; exact Formalism.MainNotions.BridgeLemma₂.c3eqv_N_X (Formalism.MainNotions.BridgeLemma₂.c3eqv_NLam_symm hn'L)
  have hnP : ∀ x, (∀ b : Fin D.R.rS, (HV D).B ((F0 X u).e b.castSucc) x = 0) → n x - x ∈ (F0 X u).X := by
    intro x hx; rw [hXF]; exact hnL.2.2 x (orth_of u hx)
  have hnsP : ∀ x, (∀ b : Fin D.R.rS, (HV D).B ((F0 X u).e b.castSucc) x = 0) → n.symm x - x ∈ (F0 X u).X := by
    intro x hx; rw [hXF]; exact (Formalism.MainNotions.BridgeLemma₂.c3eqv_NLam_symm hnL).2.2 x (orth_of u hx)
  have hn'P : ∀ x, (∀ b : Fin D.R.rS, (HV D).B ((F0 X u).e b.castSucc) x = 0) → n' x - x ∈ (F0 X u).X := by
    intro x hx; rw [hXF]; exact hn'L.2.2 x (orth_of u hx)
  have hn : ∀ x y, (HV D).B (n x) (n y) = (HV D).B x y := fun x y => hnL.1.1 y x
  have hG₂ : ∀ c, (Ft t₂).e c = n (t₁.lin (a (n' ((F0 X u).e c)))) := by
    intro c; rw [Ft_e', hlin]; rfl
  have hemb : ∀ w : W, ∀ c, (HV D).B ((F0 X u).e c) (W.subtype w) = 0 :=
    fun w => (hEmb.2 _).2 (Submodule.mem_sup_left ⟨w, rfl⟩)
  have hkey : ∀ w : W, a (w : (VS D).V) - w ∈ (F0 X u).X := by
    intro w
    obtain ⟨y₁, hy₁, hy₁p, hy₁v⟩ := hH₁ w
    obtain ⟨y₂, hy₂, hy₂p, hy₂v⟩ := hH₂ w
    have hy₂v' : y₂ - n (t₁.lin (a (n' (W.subtype w)))) ∈ (Ft t₂).X := by
      rw [hlin] at hy₂v; exact hy₂v
    exact core (F0 X u) (Ft t₁) (Ft t₂) t₁.lin n n' a (Ft_e' t₁) hG₂ hn hnX hnP hnsX hnsP hn'X hn'P hn'sX
      ha_fix hI (hemb w) (hemb (h w)) hy₁ hy₁p hy₁v hy₂ hy₂p hy₂v'

  have hafX : ∀ x ∈ (F0 X u).X, a x = x := fun x hx => fix_X (a : (VS D).V →ₗ[D.host.E] (VS D).V) ha_fix hx
  have haL : a ∈ NLam t₁.lam' (lf D (X.Fu u)) := by
    refine ⟨⟨ha_isom, ha_gmap⟩, fun j x hx => ?_, fun x hx => ?_⟩
    · have hxX : x ∈ (F0 X u).X := by
        rw [hXF]
        refine (Submodule.span_mono ?_) hx
        rintro _ ⟨i, -, rfl⟩; exact ⟨i, rfl⟩
      rw [hafX x hxX, sub_self]; exact Submodule.zero_mem _
    · have hxP := of_orth u hx
      set F := F0 X u
      have hzz : (HV D).B F.z F.z ≠ 0 := by rw [FlagD.z, F.zz]; exact neg_ne_zero.2 F.hT
      set c := (HV D).B x F.z / (HV D).B F.z F.z
      set x' := x - c • F.z
      have hx'c : ∀ k, (HV D).B (F.e k) x' = 0 := by
        intro k
        refine B_sw ?_
        refine Fin.lastCases ?_ (fun b => ?_) k
        · change (HV D).B x' F.z = 0
          simp only [x', c, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
          field_simp
          ring
        · simp only [x', map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
          have hz0 : (HV D).B F.z (F.e b.castSucc) = 0 := B_sw (F.zperp b)
          rw [B_sw (hxP b), hz0]
          simp
      obtain ⟨y, hy, x0, hx0, hyx⟩ := Submodule.mem_sup.1 ((hEmb.2 x').1 hx'c)
      obtain ⟨w, rfl⟩ := hy
      have hz : a F.z = F.z := ha_fix (Fin.last _)
      have ex : x = W.subtype w + x0 + c • F.z := by rw [hyx]; simp [x']
      have : a x - x = a (W.subtype w) - W.subtype w := by
        rw [ex, map_add, map_add, map_smul, hz, hafX x0 hx0]; abel
      rw [this, ← hXF]
      exact hkey w
  refine GlobalTheory.TypeAsm.eqC_holds D X Y u t₁ t₂ hlam hEq' ⟨n, hnL, n'.trans a,
    Formalism.MainNotions.BridgeLemma₂.c3eqv_NLam_trans hn'L haL, ?_⟩
  rw [hlin]
  ext x; rfl

end GlobalTheory.TypeAsm.InjProof
