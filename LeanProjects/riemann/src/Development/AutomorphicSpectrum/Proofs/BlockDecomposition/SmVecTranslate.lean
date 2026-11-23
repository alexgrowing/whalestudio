import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ReadMod
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PSatTw
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PIndMap
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemRangeOfKer

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin
open GlobalTheory.CompanionTheory.NodeSep PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.NodeSep

section Geo

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ}

theorem af_ext {a : ℕ} {g h : GL (Fin a) (Af E)}
    (H : ∀ v, GeneralLinearGroup.map (pLoc E v) g = GeneralLinearGroup.map (pLoc E v) h) : g = h := by
  refine Units.ext (Matrix.ext fun i j => Subtype.ext (funext fun v => ?_))
  exact congrArg (fun x : GL (Fin a) (v.adicCompletion E) => x i j) (H v)

theorem comm_y {a : ℕ} (w : HeightOneSpectrum (𝓞 E)) {y : GL (Fin a) (Af E)}
    (hy : GeneralLinearGroup.map (pLoc E w) y = 1) (h : GL (Fin a) (w.adicCompletion E)) :
    y * locGL E a w h = locGL E a w h * y := by
  refine af_ext fun v => ?_
  by_cases e : v = w
  · subst e
    simp [map_mul, hy, pLoc_locGL]
  · simp [map_mul, pLoc_locGL_of_ne e]

theorem exists_y {a : ℕ} (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin a) (Af E)) :
    ∃ (y : GL (Fin a) (Af E)) (h : GL (Fin a) (w.adicCompletion E)),
      GeneralLinearGroup.map (pLoc E w) y = 1 ∧ g = y * locGL E a w h := by
  refine ⟨g * (locGL E a w (GeneralLinearGroup.map (pLoc E w) g))⁻¹, GeneralLinearGroup.map (pLoc E w) g, ?_, by simp⟩
  simp [map_mul, map_inv, pLoc_locGL]

theorem lev_locGL (w : HeightOneSpectrum (𝓞 E)) (m : GLw r w × GLw s w) :
    lev (Af E) r s (locGL E r w m.1, locGL E s w m.2) = locGL E (r + s) w (lev (w.adicCompletion E) r s m) := by
  refine af_ext fun v => ?_
  rw [GlobalTheory.CompanionTheory.CTFin.Slice1.map_lev]
  by_cases e : v = w
  · subst e
    simp only [pLoc_locGL]
  · simp only [pLoc_locGL_of_ne e]
    exact map_one _

theorem lev_lw (w : HeightOneSpectrum (𝓞 E)) (m : GLw r w × GLw s w) :
    lev (Ad E) r s (lw w m) = embW (r + s) w (lev (w.adicCompletion E) r s m) := by
  change lev (Ad E) r s (finGL E r (locGL E r w m.1), finGL E s (locGL E s w m.2)) = finGL E (r + s) _
  rw [GlobalTheory.CompanionTheory.CTFin.Slice1.lev_finGL, lev_locGL]

theorem locGL_unip (w : HeightOneSpectrum (𝓞 E)) (u : BlockIx (r + s) r → w.adicCompletion E) :
    locGL E (r + s) w (unip u) = unip fun p => sLoc E w (u p) := by
  refine af_ext fun v => ?_
  rw [GlobalTheory.CompanionTheory.CTFin.IwaAd.map_unip]
  by_cases e : v = w
  · subst e
    rw [pLoc_locGL]
    congr 1
    funext p
    exact (Pi.single_eq_same (M := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E) v (u p)).symm
  · rw [pLoc_locGL_of_ne e]
    have : (fun p => pLoc E v (sLoc E w (u p))) = 0 := by
      funext p
      exact Pi.single_eq_of_ne (M := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E) e (u p)
    rw [this, unip_zero]

theorem embW_unip (w : HeightOneSpectrum (𝓞 E)) (u : BlockIx (r + s) r → w.adicCompletion E) :
    ∃ v : BlockIx (r + s) r → Ad E, embW (r + s) w (unip u) = unip v := by
  refine ⟨fun p => sFin E (sLoc E w (u p)), ?_⟩
  refine ga_ext ?_ ?_
  · rw [embW, MonoidHom.comp_apply, pInf_finGL, GlobalTheory.CompanionTheory.CTFin.IwaAd.map_unip]
    have : (fun p => pInf E (sFin E (sLoc E w (u p)))) = 0 := by
      funext p
      exact map_zero (infEq E).symm
    rw [this, unip_zero]
  · rw [embW, MonoidHom.comp_apply, pFin_finGL, GlobalTheory.CompanionTheory.CTFin.IwaAd.map_unip, locGL_unip]
    rfl

theorem chiDet_embW (χ : HChar E) {a : ℕ} (w : HeightOneSpectrum (𝓞 E)) (g : GLw a w) :
    chiDet a χ (embW a w g) = χ.loc w (GeneralLinearGroup.det g) := by
  change (χ : _ →* ℂˣ) (GeneralLinearGroup.det (finGL E a (locGL E a w g))) = _
  rw [det_finGL, finId_det_locGL]
  rfl

theorem absC_loc (z : ℂ) (w : HeightOneSpectrum (𝓞 E)) (x : (w.adicCompletion E)ˣ) :
    (Model.absC E z).loc w x = GlobalTheory.SmGL.absPow (w.adicCompletion E) z x := by
  apply Units.ext
  have hL : (((Model.absC E z).loc w x : ℂˣ) : ℂ) =
      Complex.exp (z * GlobalTheory.Mem.Chr.CharModel.logNorm E (GlobalTheory.Mem.Chr.localIdele E w x)) := rfl
  have h0 : Valued.v (x : w.adicCompletion E) ≠ 0 := by simp
  set n : ℤ := -WithZero.log (Valued.v (x : w.adicCompletion E)) with hn
  have hx : Valued.v (x : w.adicCompletion E) = WithZero.exp (-n) := by
    rw [hn, neg_neg, WithZero.exp_log h0]
  have hN : (0 : ℝ) < ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) := by
    have : (Ideal.absNorm w.asIdeal : ℕ) ≠ 0 := by simpa [Ideal.absNorm_eq_zero_iff] using w.ne_bot
    exact_mod_cast Nat.pos_of_ne_zero this
  rw [hL, GlobalTheory.SmGL.val_absPow, GlobalTheory.Mem.Chr.CharModel.logNorm_local w x n hx, GlobalTheory.LGrp.BorelCompletion.nabs_completion,
    show WithZero.log (Valued.v (x : w.adicCompletion E)) = -n by rw [hn, neg_neg]]
  have hq : ((Formalism.UG.qV E w : ℕ) : ℝ) = ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) := rfl
  rw [hq, Complex.cpow_def_of_ne_zero (by exact_mod_cast (zpow_pos hN _).ne'), ← Complex.ofReal_log (zpow_pos hN _).le, Real.log_zpow]
  congr 1
  push_cast
  ring

theorem cc_lw (w : HeightOneSpectrum (𝓞 E)) (m : GLw r w × GLw s w) :
    cc E r s (lw w m) = GlobalTheory.SmGL.deltaHalf (w.adicCompletion E) (GlobalTheory.SmGL.Two (Fin r) (Fin s))
      (GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin r) (Fin s) m) := by
  rw [GlobalTheory.SmGL.deltaHalf_two]
  have e : cc E r s (lw w m) = chiDet r (Model.absC E ((s : ℂ) / 2)) (embW r w m.1) *
      chiDet s (Model.absC E (-(r : ℂ) / 2)) (embW s w m.2) := rfl
  rw [e, chiDet_embW, chiDet_embW, absC_loc, absC_loc]
  simp

theorem parab_dec {w : HeightOneSpectrum (𝓞 E)} (p : GlobalTheory.SmGL.parab (w.adicCompletion E) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)))) :
    ∃ (u : BlockIx (r + s) r → w.adicCompletion E) (m : GLw r w × GLw s w), p.1 = unip u * lev (w.adicCompletion E) r s m ∧
      GlobalTheory.SmGL.leviProj (w.adicCompletion E) _ p = GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin r) (Fin s) m := by
  have key : ∀ q ∈ GlobalTheory.SmGL.parab (w.adicCompletion E) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s))),
      ∀ i j : Fin (r + s), r ≤ (i : ℕ) → (j : ℕ) < r → (q : Matrix _ _ (w.adicCompletion E)) i j = 0 := by
    intro q hq i j hi hj
    have := (GlobalTheory.SmGL.mem_parab_two _).1 hq (⟨i - r, by omega⟩ : Fin s) (⟨j, hj⟩ : Fin r)
    convert this using 2 <;> apply Fin.ext <;> simp
    omega
  obtain ⟨u, m, h⟩ := GlobalTheory.CompanionTheory.CTFin.IwaFin.exists_unip_mul_lev r s p.1 (key _ p.2) (key _ (inv_mem p.2))
  refine ⟨u, m, h, ?_⟩
  funext x
  cases x with
  | false =>
    refine Units.ext (Matrix.ext fun i j => ?_)
    rw [GlobalTheory.SmGL.leviProj_apply, h, GlobalTheory.SmGL.two_false, GlobalTheory.SmGL.two_false]
    have e : ∀ i : Fin r, GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) (Sum.inl i) = Fin.castAdd s i := fun i => Fin.ext (by simp)
    rw [e, e, unip_lev_cc]
    rfl
  | true =>
    refine Units.ext (Matrix.ext fun i j => ?_)
    rw [GlobalTheory.SmGL.leviProj_apply, h, GlobalTheory.SmGL.two_true, GlobalTheory.SmGL.two_true]
    have e : ∀ i : Fin s, GlobalTheory.SmGL.stdSum (rfl : r + s = r + s) (Sum.inr i) = Fin.natAdd r i := fun i => Fin.ext (by simp)
    rw [e, e, unip_lev_nn]
    rfl

theorem cf_fin_mul (k : Kinf E (r + s)) (a b : GL (Fin (r + s)) (Af E)) :
    cf (r + s) k (a * b) = finGL E (r + s) a * cf (r + s) k b := by
  rw [cf, cf, map_mul, ← mul_assoc, infGL_comm, mul_assoc]

theorem sl_law (w : HeightOneSpectrum (𝓞 E)) {φ : Sm E (r + s)}
    (hφ : ∀ (x : BlockIx (r + s) r → Ad E) g, φ.1 (unip x * g) = φ.1 g) (k : Kinf E (r + s))
    {y : GL (Fin (r + s)) (Af E)} (hy : GeneralLinearGroup.map (pLoc E w) y = 1)
    (u : BlockIx (r + s) r → w.adicCompletion E) (m₀ : GLw r w × GLw s w) (g : GLw (r + s) w) (m : GA E r × GA E s) :
    sl k (y * locGL E (r + s) w (unip u * lev (w.adicCompletion E) r s m₀ * g)) φ m =
      ((cc E r s (lw w m₀) : ℂˣ) : ℂ) * sl k (y * locGL E (r + s) w g) φ (m * lw w m₀) := by
  obtain ⟨v, hv⟩ := embW_unip w u
  obtain ⟨v', hv'⟩ := lev_mul_unip m v
  have hc := comm_y w hy
  have e0 : y * locGL E (r + s) w (unip u * lev (w.adicCompletion E) r s m₀ * g) =
      locGL E (r + s) w (unip u) * (locGL E (r + s) w (lev (w.adicCompletion E) r s m₀) * (y * locGL E (r + s) w g)) := by
    rw [map_mul, map_mul, ← mul_assoc, ← mul_assoc, hc, mul_assoc _ y, hc]
    simp only [mul_assoc]
  have hA : finGL E (r + s) (locGL E (r + s) w (unip u)) = unip v := hv
  have e : lev (Ad E) r s m * cf (r + s) k (y * locGL E (r + s) w (unip u * lev (w.adicCompletion E) r s m₀ * g)) =
      unip v' * (lev (Ad E) r s (m * lw w m₀) * cf (r + s) k (y * locGL E (r + s) w g)) := by
    rw [e0, cf_fin_mul, cf_fin_mul, hA, map_mul, lev_lw, ← mul_assoc, hv']
    simp only [mul_assoc]
    rfl
  rw [sl_apply, sl_apply, e, hφ]
  have hcc : ((cc E r s (lw w m₀) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hcm : ((cc E r s m : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  simp only [map_mul (cc E r s), mul_inv, Units.val_mul, Units.val_inv_eq_inv_val]
  field_simp

end Geo

section Gen

variable {G V : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]

def smSub (ρ : Representation ℂ G V) : Submodule ℂ V where
  carrier := {x | SmVec ρ x}
  add_mem' := by
    rintro a b ⟨U, hU, ha⟩ ⟨U', hU', hb⟩
    refine ⟨U ⊓ U', hU.inter hU', GlobalTheory.LGrp.mem_fixed.2 fun u hu => ?_⟩
    rw [map_add, GlobalTheory.LGrp.mem_fixed.1 ha u hu.1, GlobalTheory.LGrp.mem_fixed.1 hb u hu.2]
  zero_mem' := ⟨⊤, isOpen_univ, GlobalTheory.LGrp.mem_fixed.2 fun u _ => map_zero _⟩
  smul_mem' := by
    rintro c a ⟨U, hU, ha⟩
    refine ⟨U, hU, GlobalTheory.LGrp.mem_fixed.2 fun u hu => ?_⟩
    rw [map_smul, GlobalTheory.LGrp.mem_fixed.1 ha u hu]

theorem smVec_translate [IsTopologicalGroup G] (ρ : Representation ℂ G V) {x : V} (hx : SmVec ρ x) (g : G) : SmVec ρ (ρ g x) := by
  obtain ⟨U, hU, h⟩ := hx
  refine ⟨U.comap (MulAut.conj g⁻¹).toMonoidHom, hU.preimage (by
    change Continuous fun a : G => g⁻¹ * a * g⁻¹⁻¹
    fun_prop), GlobalTheory.LGrp.mem_fixed.2 fun u hu => ?_⟩
  have e := GlobalTheory.LGrp.mem_fixed.1 h _ hu
  have e' : u * g = g * ((MulAut.conj g⁻¹).toMonoidHom u) := by simp [MulAut.conj_apply, mul_assoc]
  rw [← Module.End.mul_apply, ← map_mul, e', map_mul, Module.End.mul_apply, e]

theorem isOpen_fix [IsTopologicalGroup G] (ρ : Representation ℂ G V) {x : V} {U : Subgroup G} (hU : IsOpen (U : Set G))
    (h : ∀ u ∈ U, ρ u x = x) : IsOpen {g | ρ g x = x} := by
  let H : Subgroup G :=
    { carrier := {g | ρ g x = x}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        change ρ (a * b) x = x
        rw [map_mul, Module.End.mul_apply, hb, ha]
      inv_mem' := fun {a} ha => by
        change ρ a⁻¹ x = x
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  exact H.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset (hU.mem_nhds (one_mem U)) fun u hu => h u hu)

end Gen

section Node

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r s : ℕ} {t₁ : Tr E r} {t₂ : Tr E s}

theorem node_space (t₁ : Tr E r) (t₂ : Tr E s) : (Tr.node t₁ t₂).space =
    Submodule.span ℂ {φ | MemInd2 (tw t₁.space ((s : ℂ) / 2)) (tw t₂.space (-(r : ℂ) / 2)) φ ∧
      φ ∈ GlobalTheory.DiscSpec.finVec (cptRep E (r + s))} := by
  rw [Tr.space]

theorem node_unip {φ : Sm E (r + s)} (hφ : φ ∈ (Tr.node t₁ t₂).space) (x : BlockIx (r + s) r → Ad E) (g : GA E (r + s)) :
    φ.1 (unip x * g) = φ.1 g := by
  rw [node_space] at hφ
  induction hφ using Submodule.span_induction with
  | mem φ h => exact h.1.1 x g
  | zero => rfl
  | add a b _ _ ha hb =>
    change a.1 _ + b.1 _ = a.1 g + b.1 g
    rw [ha, hb]
  | smul c a _ ha =>
    change c * a.1 _ = c * a.1 g
    rw [ha]

theorem tw_tens {V₁ : Submodule ℂ (Sm E r)} {V₂ : Submodule ℂ (Sm E s)} {F : GA E r × GA E s → ℂ}
    (hF : F ∈ tens2 (tw V₁ ((s : ℂ) / 2)) (tw V₂ (-(r : ℂ) / 2))) :
    (fun m => (((cc E r s m)⁻¹ : ℂˣ) : ℂ) * F m) ∈ tens2 V₁ V₂ := by
  induction hF using Submodule.span_induction with
  | mem F h =>
    obtain ⟨φ₁, h₁, φ₂, h₂, rfl⟩ := h
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.1 h₁
    obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.1 h₂
    refine Submodule.subset_span ⟨a, ha, b, hb, funext fun m => ?_⟩
    have e : ((cc E r s m : ℂˣ) : ℂ) = ((chiDet r (Model.absC E ((s : ℂ) / 2)) m.1 : ℂˣ) : ℂ) *
        ((chiDet s (Model.absC E (-(r : ℂ) / 2)) m.2 : ℂˣ) : ℂ) := rfl
    have h0 : ((cc E r s m : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
    change (((cc E r s m)⁻¹ : ℂˣ) : ℂ) * (a.1 m.1 * ((chiDet r (Model.absC E ((s : ℂ) / 2)) m.1 : ℂˣ) : ℂ) *
      (b.1 m.2 * ((chiDet s (Model.absC E (-(r : ℂ) / 2)) m.2 : ℂˣ) : ℂ))) = _
    rw [Units.val_inv_eq_inv_val, e] at *
    field_simp
  | zero =>
    convert Submodule.zero_mem (tens2 V₁ V₂) using 1
    funext m
    simp
  | add a b _ _ ha hb =>
    convert add_mem ha hb using 1
    funext m
    simp [mul_add]
  | smul c a _ ha =>
    convert Submodule.smul_mem _ c ha using 1
    funext m
    simp
    ring

theorem node_tens {φ : Sm E (r + s)} (hφ : φ ∈ (Tr.node t₁ t₂).space) (k : Kinf E (r + s)) (y : GL (Fin (r + s)) (Af E)) :
    sl k y φ ∈ tens2 t₁.space t₂.space := by
  rw [node_space] at hφ
  induction hφ using Submodule.span_induction with
  | mem φ h => exact tw_tens (h.1.2 k y)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

theorem node_fin {φ : Sm E (r + s)} (hφ : φ ∈ (Tr.node t₁ t₂).space) (g : GL (Fin (r + s)) (Af E)) :
    finRep E (r + s) g φ ∈ (Tr.node t₁ t₂).space := by
  rw [node_space] at hφ ⊢
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    refine Submodule.subset_span ⟨⟨fun x y => ?_, fun k y => ?_⟩, ?_⟩
    · change φ.1 (unip x * y * finGL E (r + s) g) = φ.1 (y * finGL E (r + s) g)
      rw [mul_assoc, h.1.1]
    · convert h.1.2 k (y * g) using 1
      funext m
      change φ.1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) y) * finGL E (r + s) g) = _
      rw [map_mul]
      simp only [mul_assoc]
    · have := finVec_rt h.2 1 g
      have e : cf (r + s) (1 : Kinf E (r + s)) g = finGL E (r + s) g := by simp [cf]
      rw [e] at this
      exact this
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

end Node

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r s : ℕ} {t₁ : Tr E r} {t₂ : Tr E s}

theorem slice_fixed {w : Pl E} {φ : Sm E (r + s)} (hφ : φ ∈ (Tr.node t₁ t₂).space)
    {U : Subgroup (GLw (r + s) w)} (hfix : φ ∈ GlobalTheory.PRep.fixed ((finRep E (r + s)).comp (locGL E (r + s) w)) U)
    (k : Kinf E (r + s)) (y : GL (Fin (r + s)) (Af E)) (g : GLw (r + s) w) (u : GLw (r + s) w) (hu : u ∈ U) :
    sl k (y * locGL E (r + s) w (g * u)) φ = sl k (y * locGL E (r + s) w g) φ := by
  rw [map_mul, ← mul_assoc, ← sl_fin]
  congr 1
  exact GlobalTheory.LGrp.mem_fixed.1 hfix u hu

theorem smooth_slice {w : Pl E} (h₁ : ∀ g, ∀ x ∈ t₁.space, ((finRep E r).comp (locGL E r w)) g x ∈ t₁.space)
    (h₂ : ∀ g, ∀ x ∈ t₂.space, ((finRep E s).comp (locGL E s w)) g x ∈ t₂.space)
    {φ : Sm E (r + s)} (hφ : φ ∈ (Tr.node t₁ t₂).space)
    (hs : SmVec ((finRep E (r + s)).comp (locGL E (r + s) w)) φ) (k : Kinf E (r + s))
    {y : GL (Fin (r + s)) (Af E)} (hy : GeneralLinearGroup.map (pLoc E w) y = 1) (g : GLw (r + s) w) :
    SmVec (GlobalTheory.SmGL.extTensor (GlobalTheory.PRep.sub _ t₁.space h₁) (GlobalTheory.PRep.sub _ t₂.space h₂))
      (prodInv t₁.space t₂.space (sl k (y * locGL E (r + s) w g) φ)) := by
  obtain ⟨U, hU, hfix⟩ := hs
  have hx := prodFn_prodInv (node_tens hφ k (y * locGL E (r + s) w g))
  let K := w.adicCompletion E
  let D : GLw r w × GLw s w →* ℂˣ := (GlobalTheory.SmGL.deltaHalf K (GlobalTheory.SmGL.Two (Fin r) (Fin s))).comp
    (GlobalTheory.SmGL.leviTwo K (Fin r) (Fin s)).toMonoidHom
  let C : GLw r w × GLw s w →* GLw (r + s) w := (MulAut.conj g⁻¹).toMonoidHom.comp (lev K r s)
  have hlev : Continuous (lev K r s) :=
    (GlobalTheory.SmGL.continuous_leviEmb K _).comp (GlobalTheory.SmGL.continuous_leviTwo K)
  have hC : Continuous C := by
    change Continuous fun a => g⁻¹ * lev K r s a * g⁻¹⁻¹
    exact (continuous_const.mul hlev).mul continuous_const
  have hD : IsOpen (D.ker : Set (GLw r w × GLw s w)) :=
    (GlobalTheory.SmGL.isSmoothChar_deltaHalf K).comp (GlobalTheory.SmGL.leviTwo K (Fin r) (Fin s)).toMonoidHom (GlobalTheory.SmGL.continuous_leviTwo K)
  refine ⟨U.comap C ⊓ D.ker, (hU.preimage hC).inter hD, GlobalTheory.LGrp.mem_fixed.2 fun u hu => ?_⟩
  apply prodFn_injective
  funext m
  rw [prodFn_rt, hx]
  have hl := sl_law w (fun x h => node_unip hφ x h) k hy 0 u g m
  have e1 : cc E r s (lw w u) = 1 := by
    rw [cc_lw]
    exact hu.2
  have e2 : (unip (0 : BlockIx (r + s) r → K) * lev K r s u * g : GLw (r + s) w) = g * C u := by
    rw [unip_zero, one_mul]
    simp [C, MulAut.conj_apply, mul_assoc]
  rw [e1, e2, slice_fixed hφ hfix k y g _ hu.1, Units.val_one, one_mul] at hl
  exact hl.symm

end Main

section Final

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r s : ℕ} {t₁ : Tr E r} {t₂ : Tr E s} {w : Pl E}
  {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]

theorem smVec_sub {G V : Type} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    {S : Submodule ℂ V} (h : ∀ g, ∀ x ∈ S, ρ g x ∈ S) {a : S} (ha : SmVec (GlobalTheory.PRep.sub ρ S h) a) : SmVec ρ a.1 := by
  obtain ⟨U, hU, hf⟩ := ha
  exact ⟨U, hU, GlobalTheory.LGrp.mem_fixed.2 fun u hu => congrArg Subtype.val (GlobalTheory.LGrp.mem_fixed.1 hf u hu)⟩

theorem tens_law (h₁ : ∀ g, ∀ x ∈ t₁.space, ((finRep E r).comp (locGL E r w)) g x ∈ t₁.space)
    (h₂ : ∀ g, ∀ x ∈ t₂.space, ((finRep E s).comp (locGL E s w)) g x ∈ t₂.space)
    (ℓ₁ : Sm E r →ₗ[ℂ] X) (ℓ₂ : Sm E s →ₗ[ℂ] Y) (τ₁ : Representation ℂ (GLw r w) X) (τ₂ : Representation ℂ (GLw s w) Y)
    (e₁ : ∀ g, ∀ x ∈ t₁.space, SmVec ((finRep E r).comp (locGL E r w)) x → ℓ₁ (((finRep E r).comp (locGL E r w)) g x) = τ₁ g (ℓ₁ x))
    (e₂ : ∀ g, ∀ x ∈ t₂.space, SmVec ((finRep E s).comp (locGL E s w)) x → ℓ₂ (((finRep E s).comp (locGL E s w)) g x) = τ₂ g (ℓ₂ x))
    {φ : Sm E (r + s)} (hφ : φ ∈ (Tr.node t₁ t₂).space) (hs : SmVec ((finRep E (r + s)).comp (locGL E (r + s) w)) φ)
    (k : Kinf E (r + s)) {y : GL (Fin (r + s)) (Af E)} (hy : GeneralLinearGroup.map (pLoc E w) y = 1)
    (p : GlobalTheory.SmGL.parab (w.adicCompletion E) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)))) (g : GLw (r + s) w) :
    TensorProduct.map (ℓ₁ ∘ₗ t₁.space.subtype) (ℓ₂ ∘ₗ t₂.space.subtype)
        (prodInv t₁.space t₂.space (sl k (y * locGL E (r + s) w (p.1 * g)) φ)) =
      ((GlobalTheory.SmGL.twist ((GlobalTheory.SmGL.extTensor τ₁ τ₂).comp
          (GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin r) (Fin s)).symm.toMonoidHom)
          (GlobalTheory.SmGL.deltaHalf (w.adicCompletion E) (GlobalTheory.SmGL.Two (Fin r) (Fin s)))).comp
          (GlobalTheory.SmGL.leviProj (w.adicCompletion E) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s))))) p
        (TensorProduct.map (ℓ₁ ∘ₗ t₁.space.subtype) (ℓ₂ ∘ₗ t₂.space.subtype)
          (prodInv t₁.space t₂.space (sl k (y * locGL E (r + s) w g) φ))) := by
  obtain ⟨u, m₀, hp, hl⟩ := parab_dec p
  set x := prodInv t₁.space t₂.space (sl k (y * locGL E (r + s) w g) φ) with hxd
  have hx : prodFn t₁.space t₂.space x = sl k (y * locGL E (r + s) w g) φ := prodFn_prodInv (node_tens hφ k _)
  have hx' := prodFn_prodInv (node_tens hφ k (y * locGL E (r + s) w (p.1 * g)))
  have key : prodInv t₁.space t₂.space (sl k (y * locGL E (r + s) w (p.1 * g)) φ) =
      ((cc E r s (lw w m₀) : ℂˣ) : ℂ) • GlobalTheory.SmGL.extTensor (GlobalTheory.PRep.sub _ t₁.space h₁) (GlobalTheory.PRep.sub _ t₂.space h₂) m₀ x := by
    apply prodFn_injective
    funext m
    rw [hx', map_smul, Pi.smul_apply, prodFn_rt, hx, hp]
    exact sl_law w (fun a b => node_unip hφ a b) k hy u m₀ g m
  rw [key, map_smul, tens_equiv (GlobalTheory.PRep.sub _ t₁.space h₁) (GlobalTheory.PRep.sub _ t₂.space h₂) τ₁ τ₂ _ _
    (fun g a ha => e₁ g a.1 a.2 (smVec_sub h₁ ha)) (fun g a ha => e₂ g a.1 a.2 (smVec_sub h₂ ha))
    (smooth_slice h₁ h₂ hφ hs k hy g) m₀]
  change _ = ((GlobalTheory.SmGL.deltaHalf (w.adicCompletion E) (GlobalTheory.SmGL.Two (Fin r) (Fin s))
      (GlobalTheory.SmGL.leviProj (w.adicCompletion E) _ p) : ℂˣ) : ℂ) •
    (GlobalTheory.SmGL.extTensor τ₁ τ₂) ((GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin r) (Fin s)).symm
      (GlobalTheory.SmGL.leviProj (w.adicCompletion E) _ p)) _
  rw [hl, MulEquiv.symm_apply_apply, cc_lw]

theorem exists_ind (h₁ : ∀ g, ∀ x ∈ t₁.space, ((finRep E r).comp (locGL E r w)) g x ∈ t₁.space)
    (h₂ : ∀ g, ∀ x ∈ t₂.space, ((finRep E s).comp (locGL E s w)) g x ∈ t₂.space)
    (ℓ₁ : Sm E r →ₗ[ℂ] X) (ℓ₂ : Sm E s →ₗ[ℂ] Y) (τ₁ : Representation ℂ (GLw r w) X) (τ₂ : Representation ℂ (GLw s w) Y)
    (e₁ : ∀ g, ∀ x ∈ t₁.space, SmVec ((finRep E r).comp (locGL E r w)) x → ℓ₁ (((finRep E r).comp (locGL E r w)) g x) = τ₁ g (ℓ₁ x))
    (e₂ : ∀ g, ∀ x ∈ t₂.space, SmVec ((finRep E s).comp (locGL E s w)) x → ℓ₂ (((finRep E s).comp (locGL E s w)) g x) = τ₂ g (ℓ₂ x))
    (k : Kinf E (r + s)) {y : GL (Fin (r + s)) (Af E)} (hy : GeneralLinearGroup.map (pLoc E w) y = 1) :
    ∃ Λ : Sm E (r + s) →ₗ[ℂ] GlobalTheory.SmGL.IndSp (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)))
        ((GlobalTheory.SmGL.extTensor τ₁ τ₂).comp (GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin r) (Fin s)).symm.toMonoidHom),
      ∀ φ ∈ (Tr.node t₁ t₂).space, SmVec ((finRep E (r + s)).comp (locGL E (r + s) w)) φ → ∀ g,
        (Λ φ).1.1 g = TensorProduct.map (ℓ₁ ∘ₗ t₁.space.subtype) (ℓ₂ ∘ₗ t₂.space.subtype)
          (prodInv t₁.space t₂.space (sl k (y * locGL E (r + s) w g) φ)) := by
  let T := TensorProduct.map (ℓ₁ ∘ₗ t₁.space.subtype) (ℓ₂ ∘ₗ t₂.space.subtype)
  let Sb := (Tr.node t₁ t₂).space ⊓ smSub ((finRep E (r + s)).comp (locGL E (r + s) w))
  let F : Sb → GLw (r + s) w → X ⊗[ℂ] Y := fun φ g => T (prodInv t₁.space t₂.space (sl k (y * locGL E (r + s) w g) φ.1))
  let H := GlobalTheory.SmGL.parab (w.adicCompletion E) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)))
  let σ : Representation ℂ H (X ⊗[ℂ] Y) := (GlobalTheory.SmGL.twist ((GlobalTheory.SmGL.extTensor τ₁ τ₂).comp
          (GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin r) (Fin s)).symm.toMonoidHom)
          (GlobalTheory.SmGL.deltaHalf (w.adicCompletion E) (GlobalTheory.SmGL.Two (Fin r) (Fin s)))).comp
          (GlobalTheory.SmGL.leviProj (w.adicCompletion E) (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s))))
  have hlaw : ∀ φ : Sb, F φ ∈ GlobalTheory.PRep.indSpace H σ :=
    fun φ p g => tens_law h₁ h₂ ℓ₁ ℓ₂ τ₁ τ₂ e₁ e₂ φ.2.1 φ.2.2 k hy p g
  have hop : ∀ φ : Sb, (⟨F φ, hlaw φ⟩ : GlobalTheory.PRep.indSpace H σ) ∈ GlobalTheory.PRep.smoothPart (GlobalTheory.PRep.ind H σ) := fun φ => by
    obtain ⟨U, hU, hfix⟩ := φ.2.2
    refine isOpen_fix (GlobalTheory.PRep.ind H σ) hU fun u hu => Subtype.ext (funext fun g => ?_)
    change F φ (g * u) = F φ g
    simp only [F]
    rw [slice_fixed φ.2.1 hfix k y g u hu]
  let Λ₀ : Sb →ₗ[ℂ] GlobalTheory.SmGL.IndSp (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum (rfl : r + s = r + s)))
        ((GlobalTheory.SmGL.extTensor τ₁ τ₂).comp (GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin r) (Fin s)).symm.toMonoidHom) :=
    { toFun := fun φ => ⟨⟨F φ, hlaw φ⟩, hop φ⟩
      map_add' := fun a b => Subtype.ext (Subtype.ext (funext fun g => by
        change T _ = T _ + T _
        simp only [Submodule.coe_add, map_add]))
      map_smul' := fun c a => Subtype.ext (Subtype.ext (funext fun g => by
        change T _ = c • T _
        simp only [Submodule.coe_smul, map_smul])) }
  obtain ⟨Λ, hΛ⟩ := LinearMap.exists_extend Λ₀
  refine ⟨Λ, fun φ hφ hs g => ?_⟩
  have := LinearMap.congr_fun hΛ (⟨φ, hφ, hs⟩ : Sb)
  change Λ φ = Λ₀ _ at this
  rw [this]
  rfl

end Final

end GlobalTheory.CompanionTheory.NodeSep

open GlobalTheory.CompanionTheory.NodeSep in

theorem GlobalTheory.CompanionTheory.NodeSep.nodeMod : PositivityTheory.Rg.BcB.F.RS.NodeMod := by
  intro E _ _ _ r s t₁ t₂ w X Y _ _ _ _ τ₁ τ₂ H₁ H₂
  obtain ⟨h₁, J₁, L₁, e₁, p₁⟩ := H₁
  obtain ⟨h₂, J₂, L₂, e₂, p₂⟩ := H₂
  have ex := fun (j : J₁ × J₂ × Kinf E (r + s) × {y : GL (Fin (r + s)) (Af E) // GeneralLinearGroup.map (pLoc E w) y = 1}) =>
    exists_ind (t₁ := t₁) (t₂ := t₂) h₁ h₂ (L₁ j.1) (L₂ j.2.1) τ₁ τ₂ (fun g x hx hs => e₁ j.1 g x hx hs)
      (fun g x hx hs => e₂ j.2.1 g x hx hs) j.2.2.1 j.2.2.2.2
  choose Λ hΛ using ex
  refine ⟨fun g φ hφ => node_fin hφ _, _, Λ, fun j g φ hφ hs => ?_, fun φ hφ hs h0 => ?_⟩
  · refine Subtype.ext (Subtype.ext (funext fun x => ?_))
    have hρ : ((finRep E (r + s)).comp (locGL E (r + s) w)) g φ ∈ (Tr.node t₁ t₂).space :=
      node_fin hφ (locGL E (r + s) w g)
    have hs' := smVec_translate ((finRep E (r + s)).comp (locGL E (r + s) w)) hs g
    have a1 := hΛ j _ hρ hs' x
    have a2 := hΛ j _ hφ hs (x * g)
    have e : sl j.2.2.1 (j.2.2.2.1 * locGL E (r + s) w x) (((finRep E (r + s)).comp (locGL E (r + s) w)) g φ) =
        sl j.2.2.1 (j.2.2.2.1 * locGL E (r + s) w (x * g)) φ := by
      rw [MonoidHom.comp_apply, sl_fin, map_mul, mul_assoc]
    rw [e] at a1
    exact a1.trans a2.symm
  · have hz : ∀ (k : Kinf E (r + s)) (g₀ : GL (Fin (r + s)) (Af E)) (m : GA E r × GA E s),
        φ.1 (lev (Ad E) r s m * cf (r + s) k g₀) = 0 := by
      intro k g₀ m
      obtain ⟨y, h, hy, rfl⟩ := exists_y w g₀
      have hx0 : prodInv t₁.space t₂.space (sl k (y * locGL E (r + s) w h) φ) = 0 := by
        refine tens_sep (GlobalTheory.PRep.sub _ t₁.space h₁) (GlobalTheory.PRep.sub _ t₂.space h₂)
          (fun j => L₁ j ∘ₗ t₁.space.subtype) (fun j => L₂ j ∘ₗ t₂.space.subtype)
          (fun a ha hj => Subtype.ext (p₁ a.1 a.2 (smVec_sub h₁ ha) hj))
          (fun a ha hj => Subtype.ext (p₂ a.1 a.2 (smVec_sub h₂ ha) hj))
          (smooth_slice h₁ h₂ hφ hs k hy h) fun j₁ j₂ => ?_
        have := hΛ (j₁, j₂, k, ⟨y, hy⟩) φ hφ hs h
        rw [h0] at this
        exact this.symm
      have hsl : sl k (y * locGL E (r + s) w h) φ = 0 := by
        rw [← prodFn_prodInv (node_tens hφ k _), hx0, map_zero]
      have := congrFun hsl m
      rw [sl_apply] at this
      exact (mul_eq_zero.1 this).resolve_left (Units.ne_zero _)
    refine Subtype.ext (funext fun x => ?_)
    obtain ⟨v, m, k, g, rfl⟩ := exists_decomp x
    rw [mul_assoc, node_unip hφ]
    exact hz k g m
