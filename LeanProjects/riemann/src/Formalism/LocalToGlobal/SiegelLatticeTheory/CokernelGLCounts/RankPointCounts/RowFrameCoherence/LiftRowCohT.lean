import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence.LiftRowCoh
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RelativeEquivalence.DCRelEquivAllHolds

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.RowForm

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
open PI.DCRelEquiv.UnitaryGroupMassFormula (nlam_maps_X nlam_inv nlam_mul mem_orth_iff isom_app gmap_mul' gmap_inv' gmap_one')

namespace LiftRowCohT

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem liftT_map_eq {n : S.V ≃ₗ[E] S.V} {U : Submodule E S.V} (h : ∀ x ∈ U, n x ∈ U) :
    U.map (n : S.V →ₗ[E] S.V) = U :=
  Submodule.eq_of_le_of_finrank_eq (by rintro _ ⟨y, hy, rfl⟩; exact h y hy) (LinearEquiv.finrank_map_eq n U)

theorem liftT_map_mul (a b : S.V ≃ₗ[E] S.V) (U : Submodule E S.V) :
    U.map ((a * b : S.V ≃ₗ[E] S.V) : S.V →ₗ[E] S.V) = (U.map (b : S.V →ₗ[E] S.V)).map (a : S.V →ₗ[E] S.V) := by
  rw [← Submodule.map_comp]
  rfl

theorem liftT_xsp_mapLF {T : E} (γ : S.V ≃ₗ[E] S.V) (hγ : γ ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : LFlag S r T) :
    Xsp (mapLF γ F) = (Xsp F).map (γ : S.V →ₗ[E] S.V) := by
  simp only [Xsp, mapLF, dif_pos hγ, Formalism.MainNotions.S.FlagG.X, mapFlag, Submodule.map_span, ← Set.range_comp]
  rfl

theorem liftT_xsp_eq {T : E} (F : LFlag S r T) : Xsp F = Xflag F r := by
  simp only [Xsp, Xflag, Formalism.MainNotions.S.FlagG.X, Formalism.MainNotions.S.FlagG.Xa]
  congr 1
  ext v
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, i.2, rfl⟩
  · rintro ⟨i, -, rfl⟩
    exact ⟨i, rfl⟩

variable {Λ : Submodule (𝓞 E) S.V}

theorem liftT_mem_gmap {n : S.V ≃ₗ[E] S.V} {L : Submodule (𝓞 E) S.V} {v : S.V} :
    n v ∈ Formalism.HermitianLatticesTheory.gmap n L ↔ v ∈ L := by
  constructor
  · rintro ⟨w, hw, h⟩
    have e : w = v := n.injective h
    rw [← e]
    exact hw
  · intro h
    exact ⟨v, h, rfl⟩

theorem liftT_maps {n : S.V ≃ₗ[E] S.V} {L : Submodule (𝓞 E) S.V} (h : Formalism.HermitianLatticesTheory.gmap n L = L) {v : S.V}
    (hv : v ∈ L) : n v ∈ L := by
  rw [← h]
  exact liftT_mem_gmap.2 hv

theorem liftT_gmap_inf {n : S.V ≃ₗ[E] S.V} (hn : Formalism.HermitianLatticesTheory.gmap n Λ = Λ) (U : Submodule E S.V) :
    Formalism.HermitianLatticesTheory.gmap n (Λ ⊓ toO S U) = Λ ⊓ toO S (U.map (n : S.V →ₗ[E] S.V)) := by
  ext v
  constructor
  · rintro ⟨w, ⟨hwΛ, hwU⟩, rfl⟩
    exact ⟨liftT_maps hn hwΛ, ⟨w, hwU, rfl⟩⟩
  · rintro ⟨hvΛ, ⟨w, hwU, rfl⟩⟩
    have hw : w ∈ Λ := by
      rw [← hn] at hvΛ
      exact liftT_mem_gmap.1 hvΛ
    exact ⟨w, ⟨hw, hwU⟩, rfl⟩

theorem liftT_iotaCompat {T T' : E} {F : LFlag S r T} {F₁ F₂ F₃ : LFlag S r T'} {β β' n : S.V ≃ₗ[E] S.V} {g : ℕ}
    (hc : IotaCompat Λ F F₁ F₂ β g) (hn : n ∈ NLam Λ F)
    (hX : Xsp F₃ = (Xsp F₂).map (n : S.V →ₗ[E] S.V))
    (hβΛ : ∀ x' ∈ Lrep Λ F₁, β x' ∈ Λ)
    (hβ' : ∀ x' ∈ Lrep Λ F₁, β' x' - n (β x') ∈ XLam Λ F₃) :
    IotaCompat Λ F F₁ F₃ β' g := by
  have hnΛ : Formalism.HermitianLatticesTheory.gmap n Λ = Λ := hn.1.2
  have hK : Formalism.HermitianLatticesTheory.gmap n (NgX Λ g F F₂) = NgX Λ g F F₃ := by
    unfold NgX Formalism.HermitianLatticesTheory.gmap
    rw [Submodule.map_sup, Submodule.map_sup, Submodule.map_smul'']
    have h1 := liftT_gmap_inf hnΛ (Xsp F)
    have h2 := liftT_gmap_inf hnΛ (Xsp F₂)
    unfold Formalism.HermitianLatticesTheory.gmap at h1 h2 hnΛ
    unfold XLam
    rw [h1, h2, hnΛ, liftT_map_eq (nlam_maps_X hn), ← hX]
  intro x' hx' l hl
  rw [hc x' hx' l hl]
  have hlΛ : l ∈ Λ := hl.1
  have hbx : β x' ∈ Λ := hβΛ x' hx'
  have hnl : n l - l ∈ NgX Λ g F F₃ := by
    refine Submodule.mem_sup_left (Submodule.mem_sup_right ?_)
    exact ⟨Submodule.sub_mem _ (liftT_maps hnΛ hlΛ) hlΛ, hn.2.2 l hl.2⟩
  have hd : β' x' - n (β x') ∈ NgX Λ g F F₃ := Submodule.mem_sup_right (hβ' x' hx')
  have e : l - β' x' = n (l - β x') - ((n l - l) + (β' x' - n (β x'))) := by
    rw [map_sub]
    abel
  rw [e, Submodule.sub_mem_iff_left _ (Submodule.add_mem _ hnl hd), ← hK, liftT_mem_gmap]

end Gen

section Grel

variable {D : D7} {X : HidaSetting D} {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}

theorem liftT_grel_equiv (Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V) : Equivalence (GRel X u u' F0 F0' Λ Λ') where
  refl _ := ⟨1, one_mem_NLam _ _, 1, one_mem_NLam _ _, by simp⟩
  symm := by
    rintro p q ⟨n, hn, n', hn', h⟩
    exact ⟨n⁻¹, nlam_inv hn, n'⁻¹, nlam_inv hn', by rw [h]; group⟩
  trans := by
    rintro p q r ⟨n, hn, n', hn', h⟩ ⟨m, hm, m', hm', h'⟩
    exact ⟨m * n, nlam_mul hm hn, n' * m', nlam_mul hn' hm', by rw [h', h]; group⟩

theorem liftT_grel_of_mk_eq {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V} {p q : GCar X u u' F0 F0' Λ Λ'}
    (h : Quot.mk (GRel X u u' F0 F0' Λ Λ') p = Quot.mk _ q) : GRel X u u' F0 F0' Λ Λ' p q :=
  (Equivalence.eqvGen_iff (liftT_grel_equiv Λ Λ')).1 (Quot.eqvGen_exact h)

end Grel

end LiftRowCohT

open LiftRowCohT

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)

def RatPtNeed : Prop :=
  ∀ n : (VS D).V ≃ₗ[D.host.E] (VS D).V, n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT → ∃ x : X.B.I.GA, RatLink X x n

def FrameFixNeed : Prop :=
  ∀ (s : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'))
    (y : Carrier (PD D s.lam (lf D (X.Fu u)) u')) (β : (VS D).V ≃ₗ[D.host.E] (VS D).V),
    Formalism.L2.SG.DataInst.Elig s.toTerm → Gval (lf D (X.Fu u)) y.1 ≠ 0 →
    IsPair s.lam (lf D (X.Fu u)) s.frame y.1 β (gS D) →
    Lat.s0 s.lam (lf D (X.Fu u)) s.frame y.1 β D.R.k = 1 → IsScalar s.lam (lf D (X.Fu u)) s.frame y.1 β →
      ∃ μ : (VS D).V ≃ₗ[D.host.E] (VS D).V, μ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ Formalism.HermitianLatticesTheory.gmap μ s.lam' = s.lam' ∧
        (∀ x ∈ Xsp (lf D (X.Fu u')), μ x ∈ Xsp (lf D (X.Fu u'))) ∧
        (∀ x ∈ orth (VS D) (Xsp (lf D (X.Fu u'))), μ x - x ∈ Xsp (lf D (X.Fu u'))) ∧
        DCRel s.lam (lf D (X.Fu u)) y.1 (mapLF (β * s.lin * μ) (lf D (X.Fu u')))

theorem liftTransNeed_of (hR : RatPtNeed X) (hTR : ToTermRel X u u' (X.Fu u) (X.Fu u'))
    (hF : FrameFixNeed X Y u u') : LiftTransNeed X Y u u' := by
  intro s y β hs hy hP h1 h2
  obtain ⟨μ, hμi, hμΛ, hμX, hμo, hdc⟩ := hF s y β hs hy hP h1 h2
  have hRL : IsRowLat D (X.Fu u) s.lam := (Y.rowsOK u).1 s.lam s.mem
  have hγi : s.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := s.rep.2.2.1
  have hγΛ : Formalism.HermitianLatticesTheory.gmap s.lin s.lam' = s.lam := s.rep.2.2.2.1
  have hβi : β ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hP.1.1
  have hβΛ : Formalism.HermitianLatticesTheory.gmap β s.lam = s.lam := hP.1.2
  have hδi : β * s.lin * μ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := mul_mem (mul_mem hβi hγi) hμi
  have hδΛ : Formalism.HermitianLatticesTheory.gmap (β * s.lin * μ) s.lam' = s.lam := by
    rw [gmap_mul', gmap_mul', hμΛ, hγΛ, hβΛ]
  have hPD : PD D s.lam (lf D (X.Fu u)) u' (mapLF (β * s.lin * μ) (lf D (X.Fu u'))) :=
    Formalism.L2.SG.Closed.TermStable_holds D u u' (X.Fu u) s.lam hRL y _ hdc
  obtain ⟨x, hx⟩ := hR _ hδi
  let q : GCar X u u' (X.Fu u) (X.Fu u') s.lam s.lam' := ⟨(x, β * s.lin * μ), hx, hδi, hδΛ, hPD⟩
  let s' : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') :=
    ⟨s.lam, s.mem, s.lam', s.mem', Quot.mk _ q⟩
  have hrel : GRel X u u' (X.Fu u) (X.Fu u') s.lam s.lam' s'.rep q :=
    liftT_grel_of_mk_eq (Quot.out_eq (Quot.mk (GRel X u u' (X.Fu u) (X.Fu u') s.lam s.lam') q))
  obtain ⟨n, hn, n', hn', hlin⟩ := (liftT_grel_equiv s.lam s.lam').symm hrel
  refine ⟨s', rfl, rfl, ?_, ?_⟩
  · show (⟨s.lam, s.mem, TermDef.mk _ _ _ ⟨s'.frame, s'.rep.2.2.2.2⟩⟩ : Term D u u' (X.Fu u) (Y.what₂ u)) =
      ⟨s.lam, s.mem, TermDef.mk _ _ _ y⟩
    have e1 : TermDef.mk s.lam (lf D (X.Fu u)) (PD D s.lam (lf D (X.Fu u)) u') ⟨s'.frame, s'.rep.2.2.2.2⟩ =
        TermDef.mk s.lam (lf D (X.Fu u)) (PD D s.lam (lf D (X.Fu u)) u') ⟨_, hPD⟩ :=
      Quot.sound (hTR s.lam s.lam' s'.rep q hrel)
    have e2 : TermDef.mk s.lam (lf D (X.Fu u)) (PD D s.lam (lf D (X.Fu u)) u') y =
        TermDef.mk s.lam (lf D (X.Fu u)) (PD D s.lam (lf D (X.Fu u)) u') ⟨_, hPD⟩ :=
      Quot.sound hdc
    exact congrArg (Term.mk s.lam s.mem) (e1.trans e2.symm)
  ·
    set A := Xsp (lf D (X.Fu u')) with hA
    have hs'i : s'.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := s'.rep.2.2.1
    have hlin' : s'.lin = n * (β * s.lin * μ) * n' := hlin
    have hAn' : A.map (n' : (VS D).V →ₗ[D.host.E] (VS D).V) = A := liftT_map_eq (nlam_maps_X hn')
    have hAμ : A.map (μ : (VS D).V →ₗ[D.host.E] (VS D).V) = A := liftT_map_eq hμX
    have hX3 : Xsp s'.frame = ((A.map (s.lin : (VS D).V →ₗ[D.host.E] (VS D).V)).map
        (β : (VS D).V →ₗ[D.host.E] (VS D).V)).map (n : (VS D).V →ₗ[D.host.E] (VS D).V) := by
      show Xsp (mapLF s'.lin (lf D (X.Fu u'))) = _
      rw [liftT_xsp_mapLF _ hs'i, hlin', liftT_map_mul, liftT_map_mul, hAn', liftT_map_mul, liftT_map_mul, hAμ]
    have hX2 : Xsp y.1 = (A.map (s.lin : (VS D).V →ₗ[D.host.E] (VS D).V)).map (β : (VS D).V →ₗ[D.host.E] (VS D).V) := by
      rw [liftT_xsp_eq, ← hP.2.1 D.R.rS, ← liftT_xsp_eq]
      show (Xsp (mapLF s.lin (lf D (X.Fu u')))).map _ = _
      rw [liftT_xsp_mapLF _ hγi]
    refine liftT_iotaCompat hP.2.2.2 hn (by rw [hX3, hX2]) (fun x' hx' => liftT_maps hβΛ hx'.1) ?_
    intro x' hx'
    have hw : s.lin (s.lin⁻¹ x') = x' := s.lin.apply_symm_apply x'
    set w := s.lin⁻¹ x' with hwdef
    have hwΛ : w ∈ s.lam' := by
      have := liftT_mem_gmap (n := s.lin⁻¹) (L := s.lam) (v := x') |>.2 hx'.1
      have hinv : Formalism.HermitianLatticesTheory.gmap s.lin⁻¹ s.lam = s.lam' := by
        rw [← hγΛ, ← gmap_mul', inv_mul_cancel, gmap_one']
      rw [hinv] at this
      exact this
    have hwo : w ∈ orth (VS D) A := by
      rw [mem_orth_iff]
      intro a ha
      have h0 := (mem_orth_iff.1 hx'.2) (s.lin a) (by
        show s.lin a ∈ Xsp (mapLF s.lin (lf D (X.Fu u')))
        rw [liftT_xsp_mapLF _ hγi]
        exact Submodule.mem_map_of_mem ha)
      rw [← hw, isom_app hγi] at h0
      exact h0
    have hn'w : n' w - w ∈ s.lam' ⊓ toO (VS D) A :=
      ⟨Submodule.sub_mem _ (liftT_maps hn'.1.2 hwΛ) hwΛ, hn'.2.2 w hwo⟩
    have hd : μ (n' w) - w ∈ s.lam' ⊓ toO (VS D) A := by
      have e : μ (n' w) - w = μ (n' w - w) + (μ w - w) := by
        rw [map_sub]
        abel
      rw [e]
      exact Submodule.add_mem _ ⟨liftT_maps hμΛ hn'w.1, hμX _ hn'w.2⟩
        ⟨Submodule.sub_mem _ (liftT_maps hμΛ hwΛ) hwΛ, hμo w hwo⟩
    have e : (s'.lin * s.lin⁻¹) x' - n (β x') = n (β (s.lin (μ (n' w) - w))) := by
      rw [map_sub, map_sub, map_sub, hw]
      congr 1
      show s'.lin w = _
      rw [hlin']
      rfl
    rw [e]
    have hγd : s.lin (μ (n' w) - w) ∈ s.lam := by
      rw [← hγΛ]
      exact liftT_mem_gmap.2 hd.1
    refine ⟨liftT_maps hn.1.2 (liftT_maps hβΛ hγd), ?_⟩
    show _ ∈ Xsp s'.frame
    rw [hX3]
    exact Submodule.mem_map_of_mem (Submodule.mem_map_of_mem (Submodule.mem_map_of_mem hd.2))

theorem liftRowCohC_of_frameFix (hR : RatPtNeed X) (hTR : ToTermRel X u u' (X.Fu u) (X.Fu u'))
    (hF : FrameFixNeed X Y u u') (hD : IotaDictNeed X Y u u') : LiftRowCohC X Y u u' :=
  liftRowCohC_of X Y u u' (liftTransNeed_of X Y u u' hR hTR hF) hD

end Formalism.L2.SG.Pf.RowForm
