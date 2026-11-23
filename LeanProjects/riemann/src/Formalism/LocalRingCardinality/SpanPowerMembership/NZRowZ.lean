import Formalism.LocalRingCardinality.SpanPowerMembership.NZRowY

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Examples₂

section Rec

variable {R : Ranks} (H : Host R)

variable {W : Type} [Fintype W] (u0 : W) (hcW : W → Tau2 R → HCParam R)
  (hv0 : ∀ u τ, (hcW u τ).v = (hcW u0 τ).v) (hb0 : ∀ u τ, (hcW u τ).b = (hcW u0 τ).b)
  (he0 : ∀ u τ, (hcW u τ).e = (hcW u0 τ).e)
  (hf0 : ∀ u τ (h : 0 < R.k), (hcW u τ).u ⟨0, h⟩ = (hcW u0 τ).u ⟨0, h⟩)
  (hl0 : ∀ u τ (h : 0 < R.k), (hcW u τ).u ⟨R.k - 1, by omega⟩ = (hcW u0 τ).u ⟨R.k - 1, by omega⟩)
  (Del : ℚ) (hDel : 0 < Del)
  (hgap : ∀ u (τ : Tau2 R) (l : ℕ) (h : l + 1 < R.k - 1),
    (hcW u τ).v ⟨l, by omega⟩ - (hcW u τ).v ⟨l + 1, h⟩ = 4 * Del)
  (lt : W → Fin (R.k - 2) → Bool) (hlt : Function.Injective lt)
  (hlet : ∀ u (τ : Tau2 R) (l : ℕ) (h : l < R.k - 2),
    (hcW u τ).u ⟨l + 1, by omega⟩ = (hcW u τ).v ⟨l, by omega⟩ - 1 / 2 - (if lt u ⟨l, h⟩ then Del else 0))
  (cdS : ∀ (n : ℕ) (_ : Fin n → Bool), NNReal) (hcdS : ∀ n ε, 0 < cdS n ε)
  (dsg : Tau2 R → ℝ) (hdsg : ∀ ρ, 0 < dsg ρ) (etaF : ℝ)

variable (hv : W → ℝ) (vol : @HSpace H.E _ _ H.cmStar → ℝ) (hvol : ∀ V, 0 < vol V) (K : W → ClsPkg)
  (T : W → ℕ) [hT : ∀ u, Fact (T u).Prime] (Dst : ℝ) (hD : 0 < Dst) (du : W → ℕ) (hdu : ∀ u, 0 < du u)
  (Gam : ℝ) (hG : 1 < Gam)
  (hwin : ∀ u, (memW hcW K T Dst hD du hdu Gam hG u).A.Tstar ≤ (T u : ℝ) ∧
    (T u : ℝ) ≤ (1 + 1 / ((R.f : ℝ) * R.k)) * (memW hcW K T Dst hD du hdu Gam hG u).A.Tstar)
  (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) (ht : THyp H)
  (hlev : ∀ u, T u ∈ H.levelPrimes) (hpde : ∀ u, T u ≠ H.pde ∧ T u ≠ H.pde')
  (pz : W → 𝓞 H.E) (hK : ∀ u, (pz u : H.E) ∈ H.K)
  (hpz : ∀ u, (pz u : H.E) * H.conj (pz u : H.E) = (T u : H.E))
  (hcong : ∀ u, (pz u - 1) ∈ Ideal.span {((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : 𝓞 H.E)})
  (lat : letI := H.cmStar; ∀ u i, (K u).cls i → Submodule (𝓞 H.E) ((hostSpacesOfNorm H (T u0) (pz u0) (hpz u0)).X i).V)
  (hlat : letI := H.cmStar; ∀ u i c, Submodule.IsLattice H.E (lat u i c))
  (G : LocalGap H)
  (kb : ∀ j, Tau2 R → Fin (R.sigW j).1 → ℤ) (ks : ∀ j, Tau2 R → Fin (R.sigW j).2 → ℤ)
  (tw : (@placesOf H.E _ _ H.cmStar).Pl → Bool)
  (htw : ∀ w, tw ((@placesOf H.E _ _ H.cmStar).conj w) = tw w)

variable (d Dall d0 : ℕ) (hd : d ≤ Dall) (FT : Type) [Fintype FT] [DecidableEq FT]
    (ft : Fin d → FT) (ft0 : Fin d0 → FT)

variable (Lb : Lbl H) (hT2 : ∀ u, T u ≠ 2) (per : ∀ u : W, Bool → FK ((K u).cls R.m) →ₗ[ℂ] En d →ₗ[ℂ] ℂ)
  (NuL : ∀ u : W, Submodule (𝓞 H.E) ((K u).cls 0 → H.E))
  (gat : ∀ (u : W) (w : (@placesOf H.E _ _ H.cmStar).Pl), GIdx H (T u) ((@placesOf H.E _ _ H.cmStar).resChar w) →
    Formalism.MainNotions.G.GAtP ((@placesOf H.E _ _ H.cmStar).resChar w))
  (hgat : ∀ u w h, (gat u w h).d = Fintype.card ((K u).cls 0))

variable (Wg : TwGap (hostLevelRecord H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat))

local notation "DR" => (withTw (hostLevelRecord H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat) Wg)

def fin_X : DivX DR := divXStd DR (fun _ => d0) (fun _ => eb d0) (fun _ => rfl) 1 one_pos

def fin_tw : TwForms DR where
  A := fun u _ => haveI := hT u; atTN (hcW u) (K u) (T u) Dst hD (du u) (hdu u) Gam hG
  A_T := fun _ _ => rfl
  fm := fun u μ => haveI := hT u; formsN (hcW u) (K u) (T u) Dst hD (du u) (hdu u) Gam hG (En d) (per u μ) H.φ₀ (placesOf H.E)
    (card_realPlaces_eq_degree R)
  e0 := fun _ _ => LinearEquiv.refl _ _
  twist_preserves_base_lattice := fun _ _ _ => Iff.rfl
  embed_mul_block_embedding := fun _ _ _ => rfl
  eMu0 := fun _ _ _ => LinearEquiv.refl _ _
  eMu0_lat := fun _ _ _ _ => Iff.rfl
  eMu0_emb := fun _ _ _ _ => HEq.rfl

theorem fin_nu_le (u : W) (i : ℕ) (j : ℕ) (hj : i ≤ j) :
    ∀ s c, (nuD DR u i s).colLen c ≤ R.N j := fun s c =>
  ((nuD DR u i s).colLen_anti 0 c (Nat.zero_le _)).trans ((nuD_rows DR u i s).trans
    (by show R.k + i * (R.t + 1) ≤ R.k + j * (R.t + 1); have := Nat.mul_le_mul_right (R.t + 1) hj; omega))

def fin_ent (P : EntPl DR) : KerEnt DR (fin_X H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat Wg) (fin_tw H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat Wg) where
  lam := P.lam
  iL := P.iL
  iL_lam := P.iL_lam
  iL_int := P.iL_int
  Th := fun _ _ w i _ _ => ThE (R.N i) (R.N (i + 1)) ((DR).what₂.places.resChar w)
  VQ := fun _ _ _ _ => (DR).what₂.LL
  ev := fun _ _ _ _ =>
    { toFun := fun v _ => (DR).what₂.embLL v
      map_add' := fun a b => by funext _; simp
      map_smul' := fun a b => by funext _; simp }
  ev_inj := fun _ _ _ _ a b h => (DR).what₂.embLL.injective (congrFun h ())
  prS := fun _ _ w i _ =>
    { toFun := fun v => P.iL w v • (MvPolynomial.aeval (xS (R.N i) ((DR).what₂.places.resChar w))).toLinearMap
      map_add' := fun a b => by rw [map_add, add_smul]; rfl
      map_smul' := fun a b => by rw [smul_eq_mul, map_mul, mul_smul]; rfl }
  prT := fun u _ w i _ =>
    { toFun := fun v I => P.iL w v * indC (nuD DR u i) I ℂ_[(DR).what₂.places.resChar w]
      map_add' := fun a b => by funext I; simp [add_mul]
      map_smul' := fun a b => by
        funext I
        show P.iL w (a * b) * _ = P.iL w a * (P.iL w b * _)
        rw [map_mul, mul_assoc] }
  prT_val := fun u _ w _ i _ _ v' I => by
    rcases indC_01 (nuD DR u i) I ℂ_[(DR).what₂.places.resChar w] with h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨v', by simp [h]⟩
  lat_S := by
    intro u μ w _ i _ φ
    have key : ∀ v : (DR).what₂.LL, (∀ J : KM.ColChoice (R.N i) (nuD DR u i),
        ‖P.iL w v * MvPolynomial.eval (xS (R.N i) ((DR).what₂.places.resChar w))
          (MvPolynomial.map (Int.castRingHom _) (KM.nablaX (R.N i) (nuD DR u i) J))‖ ≤ 1) ↔
        v ∈ intW (DR).what₂.places w := fun v => by
      rw [P.iL_int]
      simp only [eval_nablaX]
      constructor
      · intro h
        have := h (initC (nuD DR u i) (fin_nu_le H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat Wg u i i le_rfl))
        rwa [show (∏ s, ∏ c : Fin ((nuD DR u i s).rowLen 0), if ∀ k,
            ((initC (nuD DR u i) (fin_nu_le H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat Wg u i i le_rfl)) s c k : ℕ) = k then (1 : ℂ_[(DR).what₂.places.resChar w])
            else 0) = 1 from indC_init (nuD DR u i) _ _, mul_one] at this
      · intro h J
        rcases indC_01 (nuD DR u i) J ℂ_[(DR).what₂.places.resChar w] with h0 | h0 <;>
          · unfold indC at h0
            rw [h0]
            simpa using h
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' := (mem_locW_std DR w (ι := (K u).cls i) x).mp hx
      refine ⟨trivial, fun c => ⟨x c, rfl, fun J => ?_⟩⟩
      have := (key (x c)).mpr (hx' c) J
      rwa [← MvPolynomial.coe_aeval_eq_eval] at this
    · rintro ⟨-, h⟩
      choose v hv1 hv2 using h
      refine ⟨v, (mem_locW_std DR w (ι := (K u).cls i) v).mpr fun c => (key (v c)).mp fun J => ?_, ?_⟩
      · have := hv2 c J
        rwa [← MvPolynomial.coe_aeval_eq_eval]
      · funext c y
        exact congrFun (hv1 c) y
  levelFree_lattice_condition := by
    intro u μ w _ i _ φ
    have key : ∀ v : (DR).what₂.LL, (∀ I : KM.ColChoice (R.N (i + 1)) (nuD DR u i),
        ‖P.iL w v * indC (nuD DR u i) I ℂ_[(DR).what₂.places.resChar w]‖ ≤ 1) ↔
        v ∈ intW (DR).what₂.places w := fun v => by
      rw [P.iL_int]
      constructor
      · intro h
        have := h (initC (nuD DR u i) (fin_nu_le H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat Wg u i (i + 1) (Nat.le_succ i)))
        rwa [indC_init, mul_one] at this
      · intro h I
        rcases indC_01 (nuD DR u i) I ℂ_[(DR).what₂.places.resChar w] with h0 | h0 <;>
          · rw [h0]
            simpa using h
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx' := (mem_locW_std DR w (ι := (K u).cls (i + 1)) x).mp hx
      exact ⟨trivial, fun c => ⟨x c, rfl, (key (x c)).mpr (hx' c)⟩⟩
    · rintro ⟨-, h⟩
      choose v hv1 hv2 using h
      refine ⟨v, (mem_locW_std DR w (ι := (K u).cls (i + 1)) v).mpr fun c => (key (v c)).mp (hv2 c), ?_⟩
      funext c y
      exact congrFun (hv1 c) y
  un := fun _ _ _ _ _ _ => 1
  un_ne := fun _ _ _ _ _ _ => one_ne_zero
  kform := by
    intro u μ w _ i _ c c' v v' hvv I
    have h3 : ((DR).chTw u μ).Kmap i c c' (fun _ => (DR).what₂.embLL v) = fun _ => (DR).what₂.embLL v :=
      chainN_Kmap (hcW u) (K u) i c c' _
    have h4 : (DR).what₂.embLL v' = ((DR).chTw u μ).Kmap i c c' (fun _ => (DR).what₂.embLL v) () := congrFun hvv ()
    have h2 : (DR).what₂.embLL v' = (DR).what₂.embLL v := by rw [h4, h3]
    have hv' : v' = v := (DR).what₂.embLL.injective h2
    subst hv'
    have e1 : MvPolynomial.aeval (xS (R.N i) ((DR).what₂.places.resChar w))
        (KM.applyAt0 (R.N i) (R.N (i + 1)) ((DR).what₂.places.resChar w) (ThE (R.N i) (R.N (i + 1)) _)
          (KM.Gxz (R.N i) (R.N (i + 1)) (nuD DR u i) I)) = indC (nuD DR u i) I ℂ_[(DR).what₂.places.resChar w] := by
      change MvPolynomial.eval (xS (R.N i) ((DR).what₂.places.resChar w)) _ = _
      rw [eval_applyAt0]
      erw [eval_Gxz _ _ _ _ (fin_nu_le H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat Wg u i i le_rfl)]
      rfl
    show P.iL w v' * indC (nuD DR u i) I _ = 1 * (P.iL w v' * MvPolynomial.aeval (xS (R.N i)
      ((DR).what₂.places.resChar w)) (KM.applyAt0 (R.N i) (R.N (i + 1)) ((DR).what₂.places.resChar w)
        (ThE (R.N i) (R.N (i + 1)) _) (KM.Gxz (R.N i) (R.N (i + 1)) (nuD DR u i) I)))
    rw [e1, one_mul]

theorem fin_ent_nonempty : Nonempty (KerEnt DR (fin_X H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat Wg) (fin_tw H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat Wg)) :=
  (entPl_nonempty DR).map (fin_ent H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat Wg)

theorem fin_rrDef : DV.RRDef DR := row_rrDef H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat
theorem fin_lamDef : DV.LamDef DR := row_lamDef H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat
theorem fin_buDef : Rows.BuDefQ (DR).what₂ := row_buDef H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat
theorem fin_kapR : DV.KapRBase (fin_X H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat Wg) := by
  have hi : (RowSide.sharp DR).iota (DR).what₂.mu0 = (LinearMap.id : En d →ₗ[ℂ] En d) :=
    (sharp_iota DR _).trans (rowsN_iota (hd := hd) _)
  exact (kapOf_one (RowSide.sharp DR) _ (iiStar_id _ rfl (fun x y => by rw [hi]; rfl)
    (by rw [hi]; exact Function.surjective_id)) (fun _ _ => rfl)).symm

theorem fin_memTjL (μ j) (x : Fin d0 → H.E) :
    x ∈ Idx.TjL DR μ j ↔ x ∈ (@stdH H.E _ _ H.cmStar d0).L := by
  letI : StarRing H.E := H.cmStar
  have hset : ∀ y : Fin d0 → H.E, (DR).what₂.jMt μ j y ∈ (DR).what₂.TjSet μ j ↔ y ∈ (stdH H.E d0).L := fun y => by
    have e : (DR).what₂.TjSet μ j = (oB (eb d0) (H.φ₀.comp (algebraMap (𝓞 H.E) H.E))).carrier := rowsN_TjSet (hd := hd) μ j
    rw [e]
    exact jB_mem_oB H.φ₀ (eb d0) (algebraMap (𝓞 H.E) H.E) (row_OFull H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat) y
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact (hset y).mp hy
    | zero => exact zero_mem _
    | add y z _ _ hy hz => exact add_mem hy hz
    | smul a y _ hy =>
      exact (stdH H.E d0).L.smul_mem a hy
  · intro hx
    exact Submodule.subset_span ((hset x).mpr hx)

theorem fin_idx : IdxDefs DR (fin_X H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat Wg) := by
  letI : StarRing H.E := H.cmStar
  refine ⟨fun μ j w _ _ => (ijIdx_zero _ μ j w ?_).symm, fun μ j w _ _ => (jwIdx_zero DR μ j w ?_).symm⟩
  · ext y
    constructor
    · intro hy
      exact ⟨y, (fin_memTjL H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat Wg μ j y).mpr hy, rfl⟩
    · rintro ⟨x, hx, e⟩
      have : y = x := jB_inj H.φ₀ (eb d0) e
      rw [this]
      exact (fin_memTjL H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat Wg μ j x).mp hx
  · ext x
    refine (fin_memTjL H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat Wg μ j x).trans ?_
    constructor
    · intro hx
      refine ⟨Submodule.subset_span ((fin_memTjL H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat Wg μ j x).mpr hx), fun a ha => ?_⟩
      exact (dual_std H.φ₀ (fun z => emb_star H H.φ₀ z) (eb d0) x).mpr hx a
        ((fin_memTjL H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat Wg μ j a).mp ha)
    · rintro ⟨-, h⟩
      exact (dual_std H.φ₀ (fun z => emb_star H H.φ₀ z) (eb d0) x).mp fun a ha =>
        h a ((fin_memTjL H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat Wg μ j a).mpr ha)

def fin_amb : AmbForm DR (RowSide.sharp DR) := ambOf DR _ (fun _ => d) (fun _ => eb d) (fun _ => rfl)

def fin_char : CentralCharacterOne DR := ⟨(levelRecordCentralCharacterOne H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat).χ, (levelRecordCentralCharacterOne H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat).cen, (levelRecordCentralCharacterOne H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat).one⟩

def finiteBaseSide : BaseLevelRowSide DR := standardBaseSide DR (fin_char H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat Wg)
theorem fin_rr0Def : (finiteBaseSide H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat Wg).s.RRDef := standardBaseSide_latticeDefined DR _ (row_OFull H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat)
def finiteAmbientForm : AmbForm DR (finiteBaseSide H u0 hcW hv0 hb0 he0 hf0 hl0 Del hDel hgap lt hlt hlet cdS hcdS dsg hdsg etaF hv vol hvol K T Dst hD du hdu Gam hG hwin hg ht hlev hpde pz hK hpz hcong lat hlat G kb ks tw htw d Dall d0 hd FT ft ft0 Lb hT2 per NuL gat hgat Wg).s := standardAmbientForm DR _

end Rec

end Formalism.BasicNotions.Examples₂.NZ
