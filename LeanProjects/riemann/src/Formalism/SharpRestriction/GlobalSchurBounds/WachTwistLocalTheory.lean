import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Formalism.LocalRingCardinality.DataKerP
import Formalism.LocalRingCardinality.DataDIV
import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw

noncomputable section

namespace Formalism.MainNotions.product_first_zeroth_parts

open Formalism.BasicNotions Classical NumberField

section Gen

variable {R : Ranks} {LL : Type} [Field LL] [NumberField LL] [StarRing LL] {embLL : LL →+* ℂ}
  {Pl : Rows.Places LL} {Tau : Type} [Fintype Tau] {hc : Tau → HCParam R}
  {C : ColumnChain R Tau hc} {A : ColumnsAtT R C} {P : PeriodMap R C}
  (M : MemberForms LL embLL Pl Tau hc C A P)

instance glvModFin (i : ℕ) (v : A.vT) (c : C.cls i) : Module.Finite (A.Fv v) (M.lv i v c) :=
  Module.finite_of_finrank_pos (by rw [M.lv_rank]; exact R.N_pos i)

instance glvFintype (i : ℕ) (v : A.vT) (c : C.cls i) : Fintype (M.lv i v c) :=
  haveI : Finite (M.lv i v c) := Module.finite_of_finite (A.Fv v)
  Fintype.ofFinite _

instance glkModFin (i : ℕ) (v : A.vT) (c : C.cls i) : Module.Finite (A.Fv v) (M.lk i v c) :=
  Module.finite_of_finrank_pos (by rw [M.lk_rank]; exact R.N_pos i)

instance glkDualFintype (i : ℕ) (v : A.vT) (c : C.cls i) : Fintype (Module.Dual (A.Fv v) (M.lk i v c)) :=
  haveI : Finite (Module.Dual (A.Fv v) (M.lk i v c)) := Module.finite_of_finite (A.Fv v)
  Fintype.ofFinite _

def gUop (i : ℕ) (v : A.vT) : (C.cls i → C.Y i → ℂ) →ₗ[ℂ] (C.cls i → C.Y i → ℂ) :=
  LinearMap.pi fun c => ∑ x ∈ Finset.univ.filter (fun x : M.lv i v c => M.fv i v c x = 1),
    (M.upT i v c x).toLinearMap ∘ₗ LinearMap.proj (M.up i v c x)

def gDop (i : ℕ) (v : A.vT) : (C.cls i → C.Y i → ℂ) →ₗ[ℂ] (C.cls i → C.Y i → ℂ) :=
  LinearMap.pi fun c => ∑ g ∈ Finset.univ.filter
      (fun g : Module.Dual (A.Fv v) (M.lk i v c) => g (M.te i v c) = 1),
    (M.dnT i v c g).toLinearMap ∘ₗ LinearMap.proj (M.dn i v c g)

def gdia (i : ℕ) (v : A.vT) (a : (A.Fv v)ˣ) : (C.cls i → C.Y i → ℂ) →ₗ[ℂ] (C.cls i → C.Y i → ℂ) :=
  LinearMap.pi fun c => (M.dilT i v a c).toLinearMap ∘ₗ LinearMap.proj (M.dil i v a c)

def gNm (i : ℕ) (v : A.vT) : (C.cls i → C.Y i → ℂ) →ₗ[ℂ] (C.cls i → C.Y i → ℂ) := ∑ a : (A.Fv v)ˣ, gdia M i v a

def gMramI (i : ℕ) : Submodule ℂ (C.cls i → C.Y i → ℂ) := M.Fi i ⊓ ⨅ v, LinearMap.ker (gNm M i v)

def gVV (tp : Finset Tau) (w : Pl.Pl) : Finset A.vT :=
  if M.seenP w then Finset.univ.filter (fun v => M.tauOf w v ∈ tp) else ∅

def gUprod (tp : Finset Tau) (i : ℕ) (w : Pl.Pl) : (C.cls i → C.Y i → ℂ) →ₗ[ℂ] (C.cls i → C.Y i → ℂ) :=
  (gVV M tp w).toList.foldr (fun v g => (gUop M i v).comp g) LinearMap.id

def gInto {i j : ℕ} (w : Pl.Pl) (f : (C.cls i → C.Y i → ℂ) → (C.cls j → C.Y j → ℂ))
    (X : Submodule (intW Pl w) (M.lat i).V) (Y : Submodule (intW Pl w) (M.lat j).V) : Prop :=
  ∀ x ∈ X, ∃ y ∈ Y, M.emb j y = f (M.emb i x)

def gIsBfam (tp : Finset Tau) (W : Tau → ℕ) (i : ℕ) (w : Pl.Pl)
    (BV : Finset A.vT → Submodule (intW Pl w) (M.lat i).V) : Prop :=
  BV ∅ = M.S i w ∧ (∀ v, BV {v} = M.Bw i w v) ∧
  (∀ V v, v ∈ V → gInto M w (gUop M i v) (BV V) (BV (V.erase v)) ∧
    gInto M w (gDop M i v) (BV (V.erase v)) (BV V)) ∧
  (∀ V v, v ∈ V → M.tauOf w v ∉ tp →
    gInto M w (fun φ => ((A.T : ℂ) ^ (2 * W (M.tauOf w v) + R.t)) • φ) (BV V) (BV (V.erase v)))

def glossK (W : Tau → ℕ) (Cc : ℝ) : ℕ := ⌊∑ τ, (2 * (W τ : ℝ) + Cc * R.N R.m)⌋₊

def gT3withWeights (tp : Finset Tau) (W : Tau → ℕ) (Cc : ℝ) : Prop :=
  ∀ w, Pl.resChar w = A.T →
    (∀ i, i < R.m →
      (M.seenP w = false →
        gInto M w (fun φ => ((A.T : ℂ) ^ (glossK (R := R) W Cc)) • C.Klin i φ) (M.S i w) (M.S (i + 1) w)) ∧
      (M.seenP w = true → ∃ BV, gIsBfam M tp W (i + 1) w BV ∧
        gInto M w (fun φ => ((A.T : ℂ) ^ (glossK (R := R) W Cc)) • C.Klin i φ) (M.S i w) (BV Finset.univ)) ∧
      (∃ e1 : ℕ, (e1 : ℝ) ≤ 4 * ∑ τ, (W τ : ℝ) + Cc * R.f * R.N R.m ∧
        gInto M w (fun φ => ((A.T : ℂ) ^ e1) • gUprod M tp (i + 1) w (C.Klin i φ))
          (M.S i w) (M.S (i + 1) w))) ∧
    (∀ i, i ≤ R.m → M.seenP w = true → ∀ v, M.tauOf w v ∉ tp →
      gInto M w (fun φ => ((A.T : ℂ) ^ (2 * W (M.tauOf w v) + R.t)) • φ) (M.Bw i w v) (M.S i w))

def gT4with (bd : Pl.Pl → A.vT → ℝ) : Prop :=
  ∀ i, i < R.m → ∀ v : A.vT,
    (∃ c : LL,
      (∀ φ ∈ M.Fi i, gUop M (i + 1) v (C.Klin i φ) = embLL c • C.Klin i (gUop M i v φ)) ∧
      (∀ σ : LL →+* ℂ, ‖σ c‖ = (A.T : ℝ) ^ (((R.t : ℝ) + 1) / 2)) ∧
      (∀ w, Pl.resChar w = A.T → ∃ n : ℤ, Pl.val w c = ((n : ℤ) : WithTop ℤ) ∧
        |(n : ℝ)| ≤ (Pl.ramIdx w : ℝ) * bd w v)) ∧
    (∀ a, ∀ φ ∈ M.Fi i, C.Klin i (gdia M i v a φ) = gdia M (i + 1) v a (C.Klin i φ)) ∧
    ∀ φ ∈ gMramI M i, C.Klin i φ ∈ gMramI M (i + 1)

def gT4withWeights (W : Tau → ℕ) (Cc : ℝ) : Prop :=
  gT4with M (fun w v => (R.t : ℝ) + 1 + 2 * W (M.tauOf w v) + Cc * R.N R.m)

def klinIntertwinesUop : Prop :=
  ∀ i, i < R.m → ∀ v : A.vT, ∀ φ ∈ M.Fi i,
    gUop M (i + 1) v (C.Klin i φ) = ((((A.T : ℝ) ^ (((R.t : ℝ) + 1) / 2) : ℝ)) : ℂ) • C.Klin i (gUop M i v φ)

def gadm0 : Prop := M.DnUp ∧ M.DnFv

def gRoundUp : Prop :=
  ∀ i, i ≤ R.m → ∀ v c (x : M.lv i v c), M.fv i v c x = 1 →
    ∃ e : M.lk i v (M.up i v c x) ≃ₗ[A.Fv v] M.lv i v c,
      e (M.te i v (M.up i v c x)) = x ∧
      M.dn i v (M.up i v c x) ((M.fv i v c).comp e.toLinearMap) = c ∧
      ∀ φ ∈ M.Fi i,
        M.upT i v c x (M.dnT i v (M.up i v c x) ((M.fv i v c).comp e.toLinearMap)
          (φ (M.dn i v (M.up i v c x) ((M.fv i v c).comp e.toLinearMap)))) = φ c

def gRoundDn : Prop :=
  ∀ i, i ≤ R.m → ∀ v c (g : Module.Dual (A.Fv v) (M.lk i v c)), g (M.te i v c) = 1 →
    ∃ e : M.lv i v (M.dn i v c g) ≃ₗ[A.Fv v] M.lk i v c,
      M.fv i v (M.dn i v c g) = g.comp e.toLinearMap ∧
      M.up i v (M.dn i v c g) (e.symm (M.te i v c)) = c ∧
      ∀ φ ∈ M.Fi i,
        M.dnT i v c g (M.upT i v (M.dn i v c g) (e.symm (M.te i v c))
          (φ (M.up i v (M.dn i v c g) (e.symm (M.te i v c))))) = φ c

def gTrIso : Prop :=
  ∀ i, i ≤ R.m → ∀ v c, ∀ φ ∈ M.Fi i, ∀ ψ ∈ M.Fi i,
    (∀ x : M.lv i v c, M.fv i v c x = 1 →
      M.ipV i c (M.upT i v c x (φ (M.up i v c x))) (M.upT i v c x (ψ (M.up i v c x))) =
        M.ipV i (M.up i v c x) (φ (M.up i v c x)) (ψ (M.up i v c x))) ∧
    (∀ g : Module.Dual (A.Fv v) (M.lk i v c), g ≠ 0 →
      M.ipV i c (M.dnT i v c g (φ (M.dn i v c g))) (M.dnT i v c g (ψ (M.dn i v c g))) =
        M.ipV i (M.dn i v c g) (φ (M.dn i v c g)) (ψ (M.dn i v c g))) ∧
    ∀ a : (A.Fv v)ˣ,
      M.ipV i c (M.dilT i v a c (φ (M.dil i v a c))) (M.dilT i v a c (ψ (M.dil i v a c))) =
        M.ipV i (M.dil i v a c) (φ (M.dil i v a c)) (ψ (M.dil i v a c))

def gDiaMul : Prop :=
  ∀ i, i ≤ R.m → ∀ v, ∀ φ ∈ M.Fi i,
    gdia M i v 1 φ = φ ∧ ∀ a b, gdia M i v (a * b) φ = gdia M i v a (gdia M i v b φ)

def gadmT : Prop := gRoundUp M ∧ gRoundDn M ∧ gTrIso M ∧ gDiaMul M

end Gen

section Fm

variable (D : D7) (u : D.what₂.Word)

theorem gUop_fm (i : ℕ) (v : (D.mem u).A.vT) : gUop (D.fm u) i v = Uop D u i v := rfl
theorem gDop_fm (i : ℕ) (v : (D.mem u).A.vT) : gDop (D.fm u) i v = Dop D u i v := rfl
theorem gdia_fm (i : ℕ) (v : (D.mem u).A.vT) (a) : gdia (D.fm u) i v a = dia D u i v a := rfl
theorem gMramI_fm (i : ℕ) : gMramI (D.fm u) i = MramI D u i := rfl
theorem gUprod_fm (i : ℕ) (w) : gUprod (D.fm u) (tops D) i w = Uprod D u i w := rfl
theorem general_t3_of_forms_iff (Cc : ℝ) : gT3withWeights (D.fm u) (tops D) (Wt D u) Cc ↔ PointsLemma D u Cc := Iff.rfl
theorem general_t4_of_forms_iff (Cc : ℝ) : gT4withWeights (D.fm u) (Wt D u) Cc ↔ Conclusion4 D u Cc := Iff.rfl
theorem general_t4_exact_of_forms_iff : klinIntertwinesUop (D.fm u) ↔ LevelChainUOperatorCommutation D u := Iff.rfl
theorem general_adm0_of_forms_iff : gadm0 (D.fm u) ↔ UpDownIncidenceInverse D u := Iff.rfl
theorem gadmT_fm : gadmT (D.fm u) ↔ admT D u := Iff.rfl

end Fm

section Tw

variable (D : D7)

def UnrT (Dx : DivX D) (u : D.what₂.Word) (μ : D.what₂.Tup) : Prop := (D.mem u).A.T ∉ Dx.Qp μ

def UnrAllT (Dx : DivX D) : Prop := ∀ u μ, UnrT D Dx u μ

theorem unramified_at_reference_tuple (Dx : DivX D) (u : D.what₂.Word) : UnrT D Dx u D.what₂.mu0 := by
  unfold UnrT; rw [Dx.degreeZero_partial_set_empty]; exact Finset.notMem_empty _

variable {D}

theorem lamTw_eq (T : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (j : ℕ) (hj : j ≤ D.R.m) (τ : D.what₂.Tau) :
    (T.fm u μ).lam j τ = (D.fm u).lam j τ := by
  have h : ((T.fm u μ).lam j τ).w = ((D.fm u).lam j τ).w := by
    funext i
    have h1 := (T.fm u μ).lam_eq j hj τ i
    have h2 := (D.fm u).lam_eq j hj τ i
    exact_mod_cast h1.trans h2.symm
  cases h1 : (T.fm u μ).lam j τ
  cases h2 : (D.fm u).lam j τ
  simp only [h1, h2] at h
  subst h
  rfl

variable (D)

def BaseConventionGeneral (u : D.what₂.Word) (cl : ℕ → Type)
    (lat : letI := D.host.cmStar; ∀ i, cl i → Submodule (𝓞 D.host.E) (D.sp.X i).V) (det : ∀ i, cl i → D.Dt) : Prop :=
  letI := D.host.cmStar
  ∃ π : 𝓞 D.host.E, (π : D.host.E) ∈ D.host.K ∧
    (π : D.host.E) * D.host.conj (π : D.host.E) = ((D.mem u).A.T : D.host.E) ∧
    (∀ w, OverT D u w → ((D.fm u).seenP w = true ↔ 0 < D.what₂.places.val w (D.embE (π : D.host.E)))) ∧
    ∀ i, i ≤ D.R.m →
      ∃ (co : (D.sp.X i).V ≃ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)) (L0 : SDLat D.host.E (D.R.N i)),
        (∀ x y, stdH D.host.E (D.R.N i) (co x) (co y) = (D.sp.X i).hT x y) ∧
        (∀ y, co y ∈ L0.1 ↔ y ∈ (D.sp.X i).L0) ∧
        ∀ c : cl i, ∃ Ln : SDLat D.host.E (D.R.N i),
          (∀ y, co y ∈ Ln.1 ↔ ∃ a ∈ lat i c, ∃ b ∈ Formalism.HermitianLatticesTheory.dual (D.sp.X i).hT (lat i c),
            y = a + D.host.conj (π : D.host.E) • b) ∧
          (QuotientGroup.mk (det i c) : D.Dt ⧸ D.UO) = D.relDet (D.R.N i) L0 Ln

theorem base_convention_general_of_forms_iff (u : D.what₂.Word) :
    BaseConventionGeneral D u (fun i => (D.mem u).C.cls i) (D.clsLat u) (D.detCls u) ↔ admB D u := Iff.rfl

structure PendTw (u : D.what₂.Word) (μ : D.what₂.Tup) where

  clsLat : letI := D.host.cmStar; ∀ i, (D.chTw u μ).cls i → Submodule (𝓞 D.host.E) (D.sp.X i).V
  clsLat_lat : letI := D.host.cmStar; ∀ i c, Submodule.IsLattice D.host.E (clsLat i c)

  detCls : ∀ i, (D.chTw u μ).cls i → D.Dt

  xi : D.Dt →* ℂˣ
  xi_fin : ∃ n : ℕ, 0 < n ∧ ∀ x, xi x ^ n = 1
  trueColumnChoices_heckeChar_reference_eq_one : μ = D.what₂.mu0 → xi = 1

  rhoDet_eq_inv_muTilde_chiD_pow : ∀ i (c : (D.chTw u μ).cls i),
    (D.chTw u μ).rhoDet i c = (((D.muTil (i + 1) (detCls i c) * xi (detCls i c))⁻¹ *
      (D.chiD (detCls i c)) ^ (-(((D.R.N (i + 1)) / 2 : ℕ) : ℤ)) : ℂˣ) : ℂ)
  rhoDetPrime_eq_muTilde_mul_chi_pow : ∀ i (c : (D.chTw u μ).cls (i + 1)),
    (D.chTw u μ).rhoDet' i c = ((D.muTil (i + 1) (detCls (i + 1) c) * xi (detCls (i + 1) c) *
      (D.chiD (detCls (i + 1) c)) ^ ((((D.R.N i) / 2 : ℕ) : ℤ)) : ℂˣ) : ℂ)

  c0 : (D.mem u).C.cls 0 ≃ (D.chTw u μ).cls 0
  y0 : (D.mem u).C.Y 0 ≃ (D.chTw u μ).Y 0
  zero_class_lattice_eq : ∀ c, clsLat 0 (c0 c) = D.clsLat u 0 c
  zero_class_det_eq : ∀ c, detCls 0 (c0 c) = D.detCls u 0 c

  zero_identification_is_identity : ∀ φ c y, D.e0Tw u μ φ (c0 c) (y0 y) = φ c y

variable {D}

def TwistBaseConvention {u : D.what₂.Word} {μ : D.what₂.Tup} (Pn : PendTw D u μ) : Prop :=
  BaseConventionGeneral D u (fun i => (D.chTw u μ).cls i) Pn.clsLat Pn.detCls

def Tie0 (T : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) : Prop :=
  ∃ eV : (D.mem u).A.vT ≃ (T.A u μ).vT,
    (∀ w, OverT D u w → (T.fm u μ).seenP w = (D.fm u).seenP w ∧
      ∀ v, (T.fm u μ).tauOf w (eV v) = (D.fm u).tauOf w v) ∧
    ∀ v, ∀ φ ∈ (D.fm u).Fi 0, D.e0Tw u μ (Uop D u 0 v φ) = gUop (T.fm u μ) 0 (eV v) (D.e0Tw u μ φ)

def AdmTw (T : TwForms D) {u : D.what₂.Word} {μ : D.what₂.Tup} (Pn : PendTw D u μ) : Prop :=
  gadm0 (T.fm u μ) ∧ gadmT (T.fm u μ) ∧ TwistBaseConvention Pn ∧ Tie0 T u μ

def AdmETw (T : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) : Prop := ∃ Pn : PendTw D u μ, AdmTw T Pn

def TwistedT3KernelBoundAt (T : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (C : ℝ) : Prop :=
  gT3withWeights (T.fm u μ) (tops D) (Wt D u) C

def TwistedT4BoundAt (T : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (C : ℝ) : Prop :=
  gT4withWeights (T.fm u μ) (Wt D u) C

def TwistedT4ExactAt (T : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) : Prop := klinIntertwinesUop (T.fm u μ)

def colTw (u : D.what₂.Word) (μ : D.what₂.Tup) (x : Vl D u 0) : (D.chTw u μ).cls D.R.m → (D.chTw u μ).Y D.R.m → ℂ :=
  (D.chTw u μ).col (D.e0Tw u μ ((D.fm u).emb 0 x))

def TwistedT5ColumnBound (T : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (C : ℝ) : Prop :=
  ∀ w, OverT D u w →
    ∃ e : ℕ, (e : ℝ) ≤ D.R.m * (4 * ∑ τ, (Wt D u τ : ℝ) + C * D.R.f * D.R.N D.R.m) +
        ∑ v ∈ VV D u w, ((D.R.t : ℝ) + 1 + 2 * Wt D u ((D.fm u).tauOf w v) + C * D.R.N D.R.m) *
          ((D.R.m : ℝ) * (D.R.m + 1) / 2) ∧
      ∀ x ∈ Nlam D u w, ∃ y ∈ (T.fm u μ).S D.R.m w, (T.fm u μ).emb D.R.m y = tpow D u e • colTw u μ x

def SharpT5TwistColumnAt (T : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) : Prop :=
  ∀ w, OverT D u w → ∀ x ∈ Nlam D u w, Formalism.MainNotions.WeilJacquetShalikaLaw.ColGeTw T u μ w x (-((D.R.m : ℝ) * ET D u w))

def SharpT5PacketShapeAt (T : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) : Prop :=
  ∀ w, OverT D u w → ∀ (c : D.what₂.LL) (n : ℤ), D.what₂.places.val w c = ((n : ℤ) : WithTop ℤ) →
    (D.what₂.places.ramIdx w : ℝ) * ((D.R.m : ℝ) * ET D u w) ≤ (n : ℝ) →
    ∀ x ∈ Nlam D u w, ∃ y ∈ (T.fm u μ).S D.R.m w, (T.fm u μ).emb D.R.m y = D.what₂.embLL c • colTw u μ x

def TwistedT3KernelBoundAll (Dx : DivX D) (T : TwForms D) (u : D.what₂.Word) (C : ℝ) : Prop := ∀ μ, UnrT D Dx u μ → TwistedT3KernelBoundAt T u μ C
def TwistedT4Bound (Dx : DivX D) (T : TwForms D) (u : D.what₂.Word) (C : ℝ) : Prop := ∀ μ, UnrT D Dx u μ → TwistedT4BoundAt T u μ C
def TwistedT4ExactAll (Dx : DivX D) (T : TwForms D) (u : D.what₂.Word) : Prop := ∀ μ, UnrT D Dx u μ → TwistedT4ExactAt T u μ
def TwistedT5BoundAll (Dx : DivX D) (T : TwForms D) (u : D.what₂.Word) (C : ℝ) : Prop := ∀ μ, UnrT D Dx u μ → TwistedT5ColumnBound T u μ C

def TupleChainSharpColumnValuation (Dx : DivX D) (T : TwForms D) (u : D.what₂.Word) : Prop :=
  ∀ w : D.what₂.places.Pl, D.what₂.places.resChar w = (D.mem u).A.T →
    ∀ μ, D.what₂.places.resChar w ∉ Dx.Qp μ → ∀ x ∈ LT.Nlam D u w,
      Formalism.MainNotions.WeilJacquetShalikaLaw.ColGeTw T u μ w x (-((D.R.m : ℝ) * EatT D u w))

theorem sharp_t5_twist_of_each_tuple (Dx : DivX D) (T : TwForms D) (u : D.what₂.Word)
    (h : ∀ μ, UnrT D Dx u μ → SharpT5TwistColumnAt T u μ) : TupleChainSharpColumnValuation Dx T u :=
  fun w hw μ hμ x hx => h μ (by unfold UnrT; rw [← hw]; exact hμ) w hw x hx

theorem sharp_t5_twist_at_of_all (Dx : DivX D) (T : TwForms D) (u : D.what₂.Word) (h : TupleChainSharpColumnValuation Dx T u) (μ : D.what₂.Tup)
    (hμ : UnrT D Dx u μ) : SharpT5TwistColumnAt T u μ :=
  fun w hw x hx => h w hw μ (by rw [hw]; exact hμ) x hx

def TwistedBoundsAt (T : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (C : ℝ) : Prop :=
  TwistedT3KernelBoundAt T u μ C ∧ TwistedT4BoundAt T u μ C ∧ TwistedT5ColumnBound T u μ C ∧ TwistedT4ExactAt T u μ ∧ SharpT5TwistColumnAt T u μ

def TwistedBounds (Dx : DivX D) (T : TwForms D) (u : D.what₂.Word) (C : ℝ) : Prop :=
  TwistedT3KernelBoundAll Dx T u C ∧ TwistedT4Bound Dx T u C ∧ TwistedT5BoundAll Dx T u C ∧ TwistedT4ExactAll Dx T u ∧ TupleChainSharpColumnValuation Dx T u

theorem twistedBounds_of_twistedBoundsAt (Dx : DivX D) (T : TwForms D) (u : D.what₂.Word) (C : ℝ)
    (h : ∀ μ, UnrT D Dx u μ → TwistedBoundsAt T u μ C) : TwistedBounds Dx T u C :=
  ⟨fun μ hμ => (h μ hμ).1, fun μ hμ => (h μ hμ).2.1, fun μ hμ => (h μ hμ).2.2.1, fun μ hμ => (h μ hμ).2.2.2.1,
    sharp_t5_twist_of_each_tuple Dx T u fun μ hμ => (h μ hμ).2.2.2.2⟩

def TwistStatementAtTuple (Dx : DivX D) (T : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (C : ℝ) : Prop :=
  HidaSetting D u → AdmE D u → UnrT D Dx u μ → AdmETw T u μ → TwistedBoundsAt T u μ C

def TwistStatementAllTuples (Dx : DivX D) (T : TwForms D) (u : D.what₂.Word) (C : ℝ) : Prop := ∀ μ, TwistStatementAtTuple Dx T u μ C

def AdmTwAll (Dx : DivX D) (T : TwForms D) (u : D.what₂.Word) : Prop :=
  AdmE D u ∧ ∀ μ, UnrT D Dx u μ → AdmETw T u μ

theorem twisted_conclusion_of_statement (Dx : DivX D) (T : TwForms D) (u : D.what₂.Word) (C : ℝ) (h : TwistStatementAllTuples Dx T u C)
    (hS : HidaSetting D u) (hA : AdmTwAll Dx T u) : TwistedBounds Dx T u C :=
  twistedBounds_of_twistedBoundsAt Dx T u C fun μ hμ => h μ hS hA.1 hμ (hA.2 μ hμ)

def SharpT5TwistMember (Dx : DivX D) (T : TwForms D) (u : D.what₂.Word) : Prop :=
  HidaSetting D u → AdmTwAll Dx T u → TupleChainSharpColumnValuation Dx T u

theorem sharp_t5_member_of_twist_statement (Dx : DivX D) (T : TwForms D) (u : D.what₂.Word) (C : ℝ) (h : TwistStatementAllTuples Dx T u C) :
    SharpT5TwistMember Dx T u :=
  fun hS hA => (twisted_conclusion_of_statement Dx T u C h hS hA).2.2.2.2

end Tw

section Fam

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

def TwistedBoundsAlongFamily (C : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word),
    HidaSetting (Fm.D x i) u → TwistedBounds (Fm.X x i) (Fm.ex x hx i).tw u C

def AdmTwF : Prop :=
  ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word),
    AdmTwAll (Fm.X x i) (Fm.ex x hx i).tw u

def TwistFamilyStatement (C : ℝ) : Prop := AdmTwF Fm → TwistedBoundsAlongFamily Fm C

def TwistFamilyStatementExists : Prop := AdmTwF Fm → ∃ C : ℝ, TwistedBoundsAlongFamily Fm C

def TwistPointwiseFamilyConst (C : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word),
    TwistStatementAllTuples (Fm.X x i) (Fm.ex x hx i).tw u C

def TwistPointwiseFamilyExists : Prop := ∃ C : ℝ, TwistPointwiseFamilyConst Fm C

theorem twist_family_statement_of_pointwise (C : ℝ) (h : TwistPointwiseFamilyConst Fm C) : TwistFamilyStatement Fm C := by
  obtain ⟨x0, h⟩ := h
  rintro ⟨x1, hA⟩
  exact ⟨max x0 x1, fun x hx hx0 i u hS =>
    twisted_conclusion_of_statement _ _ u C (h x hx (le_trans (le_max_left _ _) hx0) i u) hS
      (hA x hx (le_trans (le_max_right _ _) hx0) i u)⟩

theorem twist_family_exists_of_pointwise (h : TwistPointwiseFamilyExists Fm) : TwistFamilyStatementExists Fm := by
  obtain ⟨C, h⟩ := h
  exact fun hA => ⟨C, twist_family_statement_of_pointwise Fm C h hA⟩

def SharpT5AllTuplesFamily : Prop :=
  ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word),
    HidaSetting (Fm.D x i) u → TupleChainSharpColumnValuation (Fm.X x i) (Fm.ex x hx i).tw u

theorem sharp_t5_family_of_twisted_family (C : ℝ) (h : TwistedBoundsAlongFamily Fm C) : SharpT5AllTuplesFamily Fm := by
  obtain ⟨x0, h⟩ := h
  exact ⟨x0, fun x hx hx0 i u hS => (h x hx hx0 i u hS).2.2.2.2⟩

def SharpT5TwistFamily : Prop :=
  ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ (i : Fm.Ix x) (u : (Fm.D x i).what₂.Word),
    SharpT5TwistMember (Fm.X x i) (Fm.ex x hx i).tw u

theorem sharp_t5_twist_family_of_pointwise (C : ℝ) (h : TwistPointwiseFamilyConst Fm C) : SharpT5TwistFamily Fm := by
  obtain ⟨x0, h⟩ := h
  exact ⟨x0, fun x hx hx0 i u => sharp_t5_member_of_twist_statement _ _ u C (h x hx hx0 i u)⟩

end Fam

def TwistStatementAbsoluteConst (𝒞 : Formalism.MainNotions.FamClass) : Prop :=
  ∃ C : ℝ, ∀ (eps : ℝ) (Fm : Formalism.MainNotions.FamP eps), 𝒞 Fm → TwistPointwiseFamilyConst Fm C

section Ref

open Formalism.BasicNotions.DV

variable {D : D7}

theorem sharp_t5_packet_shape_of_twisted (T : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (h : SharpT5TwistColumnAt T u μ) :
    SharpT5PacketShapeAt T u μ := by
  intro w hw c n hc hn x hx
  obtain ⟨y, hy, a, z, hz, rfl, ha⟩ := h w hw x hx
  have hca : (0 : WithTop ℤ) ≤ D.what₂.places.val w (c * a) := by
    by_cases h0 : a = 0
    · subst h0; simp
    · have ha' := ha.resolve_left h0
      rw [AddValuation.map_mul, hc, D.val_eq w a h0, ← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_le_coe]
      have h1 : ur D w (-((D.R.m : ℝ) * ET D u w)) =
          -((D.what₂.places.ramIdx w : ℝ) * ((D.R.m : ℝ) * ET D u w)) := by unfold ur; ring
      rw [h1] at ha'
      have h2 : (0 : ℝ) ≤ (n : ℝ) + (vAdd (D.plEq w) a : ℝ) := by linarith
      exact_mod_cast h2
  refine ⟨(⟨c * a, hca⟩ : intW D.what₂.places w) • z, Submodule.smul_mem _ _ hz, ?_⟩
  rw [Subring.smul_def]
  show (T.fm u μ).emb D.R.m ((c * a) • z) = _
  rw [mul_smul, LinearMap.map_smulₛₗ, hy]
  rfl

def ReferenceTupleIdentity (D : D7) (u : D.what₂.Word) : Prop := ∀ φ, HEq (D.e0Tw u D.what₂.mu0 φ) φ

theorem col_heq {R : Ranks} {Tau : Type} [Fintype Tau] {hc : Tau → HCParam R} {C C' : ColumnChain R Tau hc} (h : C' = C)
    (a : ℂ) (φ' : C'.cls 0 → C'.Y 0 → ℂ) (φ : C.cls 0 → C.Y 0 → ℂ) (hφ : HEq φ' φ) :
    HEq (a • C'.col φ') (a • C.col φ) := by
  subst h; rw [eq_of_heq hφ]

theorem eMu0_symm_loc (T : TwForms D) (u : D.what₂.Word) (j : ℕ) (hj : j ≤ D.R.m) (w : D.what₂.places.Pl) :
    ∀ y ∈ (T.fm u D.what₂.mu0).S j w, (T.eMu0 u j hj).symm y ∈ (D.fm u).S j w := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    refine Submodule.subset_span ?_
    exact (T.eMu0_lat u j hj _).2 (by rw [LinearEquiv.apply_symm_apply]; exact hx)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx =>
    rw [Subring.smul_def, map_smul, ← Subring.smul_def]
    exact Submodule.smul_mem _ r hx

theorem sharp_t5_of_twisted_sharp (Dx : DivX D) (T : TwForms D) (u : D.what₂.Word) (hE : ReferenceTupleIdentity D u) (h : TupleChainSharpColumnValuation Dx T u) :
    Conclusion5Sharp D u := by
  intro w hw c n hc hn x hx
  obtain ⟨y, hy, he⟩ := sharp_t5_packet_shape_of_twisted T u D.what₂.mu0 (sharp_t5_twist_at_of_all Dx T u h _ (unramified_at_reference_tuple D Dx u)) w hw c n hc hn x hx
  refine ⟨(T.eMu0 u D.R.m le_rfl).symm y, eMu0_symm_loc T u D.R.m le_rfl w y hy, ?_⟩
  have h1 := T.eMu0_emb u D.R.m le_rfl ((T.eMu0 u D.R.m le_rfl).symm y)
  rw [LinearEquiv.apply_symm_apply, he] at h1
  exact eq_of_heq (h1.symm.trans (col_heq (D.memberColumns_twistedChain_base u) _ _ _ (hE _)))

theorem sharp_t5_twist_at_place_tuple (Dx : DivX D) (T : TwForms D) (u : D.what₂.Word) (h : TupleChainSharpColumnValuation Dx T u) (w : D.what₂.places.Pl)
    (hw : OverT D u w) : ∀ x ∈ Nlam D u w,
      Formalism.MainNotions.WeilJacquetShalikaLaw.ColGeTw T u (D.what₂.muAt w) w x (-((D.R.m : ℝ) * ET D u w)) :=
  fun x hx => h w hw _ (Dx.Qp_muAt w) x hx

end Ref

end Formalism.MainNotions.product_first_zeroth_parts
