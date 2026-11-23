import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.KerIsTerm
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelChainSharpColumnValuationOfPointKernelLiftL
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemClosureIff

noncomputable section

namespace GlobalTheory.LvT.Built.ValLat

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2
open Formalism.MainNotions.product_first_zeroth_parts (Ow blk IntSpan)

variable {D : D7} {u : D.what₂.Word} {B : Built.Dat D u} {i : ℕ} {sp : Split (B.J.A i) B.J.T} {M : PtModel B.ch i}
  (R : B.Real i sp M)

def jj (w : D.what₂.places.Pl) (v : B.ch.A.vT) : (M.Lc v).K →+* D.what₂.LL :=
  (B.emb (B.Z.tauOf w (B.pr v))).comp
    ((if B.Z.seenP w then RingHom.id B.E else starRingEnd B.E).comp (R.iK v).symm.toRingHom)

theorem jj_iK (w : D.what₂.places.Pl) (v : B.ch.A.vT) (x : B.E) :
    jj R w v (R.iK v x) = B.emb (B.Z.tauOf w (B.pr v)) (if B.Z.seenP w then x else star x) := by
  unfold jj
  split_ifs <;> simp [starRingEnd_apply]

variable (M) in

def co : M.Val →ₗ[ℂ] Pol ℂ D.what₂.Tau (D.R.N i) :=
  polOf (Gr B.emb D.what₂.embLL (D.R.N i)) (shiftOf (B.lam i)) (fr0 B.emb D.what₂.embLL (D.R.N i)) ∘ₗ M.Val.subtype

theorem co_of_eq {y : M.Val} {P : Pol ℂ D.what₂.Tau (D.R.N i)}
    (h : y.1 = fnOf (Gr B.emb D.what₂.embLL (D.R.N i)) (shiftOf (B.lam i)) 1 P) : co M y = P := by
  have := GlobalTheory.TilClass.polOf_fnOf_one B.emb D.what₂.embLL (shiftOf (B.lam i)) P
  rw [← h] at this
  exact this

include R in
theorem exists_pol (y : M.Val) : ∃ F : Formalism.L2.DIV.VV ℂ (B.lam i),
    y.1 = fnOf (Gr B.emb D.what₂.embLL (D.R.N i)) (shiftOf (B.lam i)) 1 F.1 := by
  have h : y.1 ∈ ValC (Gr B.emb D.what₂.embLL (D.R.N i)) (B.lam i) := R.val_eq ▸ y.2
  obtain ⟨F, hF⟩ := (GlobalTheory.TilClass.mem_ValC_iff B.emb D.what₂.embLL (B.lam i) _).1 h
  exact ⟨F, hF.symm⟩

include R in
theorem fn_co (y : M.Val) : y.1 = fnOf (Gr B.emb D.what₂.embLL (D.R.N i)) (shiftOf (B.lam i)) 1 (co M y) := by
  obtain ⟨F, hF⟩ := exists_pol R y
  rw [co_of_eq hF, hF]

include R in
theorem co_eq_iff (y : M.Val) (F : B.V i) : co M y = MvPolynomial.map D.what₂.embLL F.1 ↔ y.1 = B.ev i F :=
  ⟨fun h => by rw [fn_co R y, h]; rfl, fun h => co_of_eq h⟩

variable (B i) in
theorem natW_lam (τ : D.what₂.Tau) : (B.ch.fm.lam i τ).natW = (B.lam i τ).natW := by
  have h := Formalism.MainNotions.product_first_zeroth_parts.natW_wSh (B.ch.fm.lam i τ) ((i : ℤ) * (((D.R.t + 1) / 2 : ℕ) : ℤ))
  rw [← h]
  rfl

variable (B i) in
theorem lamT_eq : PtModel.lamT B.ch i = B.lam i := by
  funext τ
  have h : ((i * (D.R.t + 1) / 2 : ℕ) : ℤ) = (i : ℤ) * (((D.R.t + 1) / 2 : ℕ) : ℤ) := by
    obtain ⟨c, hc⟩ := D.R.t_odd
    have h2 : D.R.t + 1 = 2 * (c + 1) := by omega
    rw [h2, Nat.mul_div_cancel_left _ two_pos, mul_left_comm, Nat.mul_div_cancel_left _ two_pos, Nat.cast_mul]
  unfold PtModel.lamT
  rw [h]
  rfl

include R in
theorem co_range : LinearMap.range (co M) = Formalism.MainNotions.product_first_zeroth_parts.CSpan (B.ch.fm.lam i) := by
  have hd : ∀ τ, delSq ℂ _ (B.ch.fm.lam i τ) = delSq ℂ _ (B.lam i τ) := fun τ => by unfold delSq; rw [natW_lam B i τ]
  have e : Formalism.MainNotions.product_first_zeroth_parts.CSpan (B.ch.fm.lam i) = CSpan (B.lam i) := by
    unfold Formalism.MainNotions.product_first_zeroth_parts.CSpan
    simp only [hd]
    rfl
  rw [e]
  ext P
  constructor
  · rintro ⟨y, rfl⟩
    have h : y.1 ∈ ValC (Gr B.emb D.what₂.embLL (D.R.N i)) (B.lam i) := R.val_eq ▸ y.2
    obtain ⟨Q, hQ, hy⟩ := h
    rwa [co_of_eq hy.symm]
  · intro hP
    have h : fnOf (Gr B.emb D.what₂.embLL (D.R.N i)) (shiftOf (B.lam i)) 1 P ∈ M.Val := by
      rw [R.val_eq]
      exact Submodule.mem_map_of_mem hP
    exact ⟨⟨_, h⟩, co_of_eq rfl⟩

variable (M) in

def wl (w : D.what₂.places.Pl) (L : Submodule (𝓞 B.E) (Fin (D.R.N i) → B.E)) : AddSubgroup M.Val where
  carrier := {y | ∃ F ∈ B.valAt w i L, y.1 = B.ev i F}
  zero_mem' := ⟨0, Submodule.zero_mem _, (map_zero (evV B.emb 1 (B.lam i) D.what₂.embLL)).symm⟩
  add_mem' := by
    rintro a b ⟨F, hF, ha⟩ ⟨G, hG, hb⟩
    exact ⟨F + G, Submodule.add_mem _ hF hG, by
      rw [Submodule.coe_add, ha, hb]; exact (map_add (evV B.emb 1 (B.lam i) D.what₂.embLL) F G).symm⟩
  neg_mem' := by
    rintro a ⟨F, hF, ha⟩
    exact ⟨-F, Submodule.neg_mem _ hF, by
      rw [Submodule.coe_neg, ha]; exact (map_neg (evV B.emb 1 (B.lam i) D.what₂.embLL) F).symm⟩

def woff (w : D.what₂.places.Pl) (z : M.Z) : AddSubgroup M.Val :=
  ⨅ (g : M.G) (b) (d : (B.I.S i).D b) (_ : (g • R.pt b d).1 = z),
    (wl M w ((B.I.S i).Lsh b d)).comap (M.act g⁻¹).toAddMonoidHom

theorem mem_woff (w : D.what₂.places.Pl) (z : M.Z) (y : M.Val) : y ∈ woff R w z ↔
    ∀ (g : M.G) (b) (d : (B.I.S i).D b), (g • R.pt b d).1 = z → M.act g⁻¹ y ∈ wl M w ((B.I.S i).Lsh b d) := by
  simp only [woff, AddSubgroup.mem_iInf, AddSubgroup.mem_comap]
  rfl

def coord (hS : B.Sees) : M.Coord where
  co := co M
  co_inj y y' h := Subtype.ext (by rw [fn_co R y, fn_co R y', h])
  co_range := co_range R
  j := jj R
  j_int w hw v x := by
    obtain ⟨x, rfl⟩ := (R.iK v).surjective x
    rw [jj_iK, R.iK_O]
    exact hS w hw _ x
  Woff := woff R

def gm (w : D.what₂.places.Pl) (v : B.ch.A.vT) (h : GL (Fin (D.R.N i)) (M.Lc v).K) : GL (Fin (D.R.N i)) D.what₂.LL :=
  if B.Z.seenP w then inside₂ _ _ (Formalism.UG.bc (jj R w v) h) else Formalism.UG.bc (jj R w v) h

theorem mov_eq (hS : B.Sees) (w : D.what₂.places.Pl) (h : ∀ v, GL (Fin (D.R.N i)) (M.Lc v).K) :
    (coord R hS).mov w h = actP (B.lam i) fun τ =>
      Formalism.UG.bc D.what₂.embLL (gm R w ((B.ch.fm.tauOf w).symm τ) (h _)) := by
  unfold PtModel.Coord.mov
  rw [blk_roundAct, lamT_eq]
  congr 1
  funext τ
  show inside₂ ℂ _ (if B.Z.seenP w = true then _ else _) = _
  unfold gm
  split_ifs
  · exact Units.ext rfl
  · exact Units.ext rfl

theorem gm_iK (w : D.what₂.places.Pl) (v : B.ch.A.vT) (g : GL (Fin (D.R.N i)) B.E) :
    gm R w v (Matrix.GeneralLinearGroup.map (R.iK v).toRingHom g) =
      if B.Z.seenP w then inside₂ _ _ (Formalism.UG.bc (B.emb (B.Z.tauOf w (B.pr v))) g)
      else Formalism.UG.bc ((B.emb (B.Z.tauOf w (B.pr v))).comp (starRingEnd B.E)) g := by
  unfold gm
  split_ifs with hs
  · congr 1
    refine Units.ext (Matrix.ext fun a b => ?_)
    exact (jj_iK R w v _).trans (by rw [if_pos hs]; rfl)
  · refine Units.ext (Matrix.ext fun a b => ?_)
    exact (jj_iK R w v _).trans (by rw [if_neg hs]; rfl)

theorem exists_map (v : B.ch.A.vT) (h : GL (Fin (D.R.N i)) (M.Lc v).K) :
    ∃ g, h = Matrix.GeneralLinearGroup.map (R.iK v).toRingHom g :=
  ⟨Matrix.GeneralLinearGroup.map (R.iK v).symm.toRingHom h,
    Units.ext (Matrix.ext fun _ _ => ((R.iK v).apply_symm_apply _).symm)⟩

theorem frame_iff (v : B.ch.A.vT) (s : Set (Fin (D.R.N i) → (M.Lc v).K)) (L : Submodule (𝓞 B.E) (Fin (D.R.N i) → B.E))
    (hs : ∀ x, (fun a => R.iK v (x a)) ∈ s ↔ x ∈ localization₂ (B.pr v).1.asIdeal L) (g : GL (Fin (D.R.N i)) B.E) :
    M.IsFrameS v (Matrix.GeneralLinearGroup.map (R.iK v).toRingHom g) s ↔ IsBasisAt (B.pr v).1 L g := by
  rw [isBasisAt_iff]
  have e : ∀ x : Fin (D.R.N i) → B.E,
      (Matrix.GeneralLinearGroup.map (R.iK v).toRingHom g).val *ᵥ (fun a => R.iK v (x a)) =
        fun a => R.iK v ((g.val *ᵥ x) a) := fun x =>
    funext fun a => (RingHom.map_mulVec (R.iK v).toRingHom g.val x a).symm
  have e2 : ∀ x : Fin (D.R.N i) → B.E, (fun a => R.iK v (x a)) ∈ (M.Lc v).std (D.R.N i) ↔
      ∀ a, (B.pr v).1.valuation B.E (x a) ≤ 1 := by
    intro x
    unfold LocF.std
    rw [Submodule.mem_pi]
    refine forall_congr' fun a => ?_
    rw [← R.iK_O, Submodule.mem_one]
    exact ⟨fun h => by obtain ⟨y, hy⟩ := h trivial; exact hy ▸ y.2, fun h _ => ⟨⟨_, h⟩, rfl⟩⟩
  unfold PtModel.IsFrameS
  constructor
  · intro h x
    rw [← hs, ← e, h, e2]
  · intro h y
    obtain ⟨x, rfl⟩ : ∃ x : Fin (D.R.N i) → B.E, y = fun a => R.iK v (x a) :=
      ⟨fun a => (R.iK v).symm (y a), funext fun a => ((R.iK v).apply_symm_apply _).symm⟩
    rw [e, hs, h, e2]

theorem gm_basis (hS : B.Sees) {w : D.what₂.places.Pl} (hw : OverT B.ch w) {L : Submodule (𝓞 B.E) (Fin (D.R.N i) → B.E)}
    (hL : Submodule.IsLattice B.E L) (v : B.ch.A.vT) {g : GL (Fin (D.R.N i)) B.E} (hg : IsBasisAt (B.pr v).1 L g) :
    IsBasisAt (D.plEq w) (dualFr (tauLat B.emb (B.ch.fm.tauOf w v) (if B.Z.seenP w then L else dual (hStd B.E _) L)))
      (gm R w v (Matrix.GeneralLinearGroup.map (R.iK v).toRingHom g)) := by
  have h := fun x => (D.val_nonneg_iff w _).symm.trans (hS w hw (B.pr v) x)
  rw [gm_iK]
  split_ifs at h ⊢ with hs
  · exact basis_seen B.emb _ _ _ h hL hg
  · exact basis_conj B.emb _ _ _ h hL hg

theorem valB_iff (hS : B.Sees) {w : D.what₂.places.Pl} (hw : OverT B.ch w) (V : Finset B.ch.A.vT) (p : M.Pt)
    {L : Submodule (𝓞 B.E) (Fin (D.R.N i) → B.E)} (hL : Submodule.IsLattice B.E L)
    (hs : ∀ v x, (fun a => R.iK v (x a)) ∈ (open Classical in
      if B.ch.fm.seenP w = true ∧ v ∉ V then ((p.2 v).1.L : Set _) else (p.2 v).ker) ↔ x ∈ localization₂ (B.pr v).1.asIdeal L)
    (y : M.Val) :
    y ∈ (coord R hS).valB w V p ↔ y ∈ wl M w (if B.Z.seenP w then L else dual (hStd B.E _) L) := by
  have hL' : Submodule.IsLattice B.E (if B.Z.seenP w then L else dual (hStd B.E _) L) := by
    split_ifs
    · exact hL
    · exact dual_lattice hL
  have key : ∀ g : B.ch.A.vT → GL (Fin (D.R.N i)) B.E, (∀ v, IsBasisAt (B.pr v).1 L (g v)) → ∀ F : B.V i,
      F ∈ B.valAt w i (if B.Z.seenP w then L else dual (hStd B.E _) L) ↔
      ∃ z ∈ localization₂ (D.plEq w).asIdeal (delStd D.what₂.LL (B.lam i)), F.1 = actP (B.lam i) (fun τ =>
        gm R w ((B.ch.fm.tauOf w).symm τ)
          (Matrix.GeneralLinearGroup.map (R.iK _).toRingHom (g ((B.ch.fm.tauOf w).symm τ)))) z := by
    intro g hg F
    refine mem_localization_delAtr B.emb (B.lam i) (D.plEq w) hL' _ (fun τ => ?_) F
    have := gm_basis R hS hw hL ((B.ch.fm.tauOf w).symm τ) (hg _)
    rwa [Equiv.apply_symm_apply] at this
  constructor
  · rintro ⟨h, hh, z, hz, e⟩
    choose g hg using fun v => exists_map R v (h v)
    obtain rfl : h = _ := funext hg
    obtain ⟨z₀, hz₀, rfl⟩ := (mem_intSpan_iff D w _ _ (natW_lam B i) z).1 hz
    rw [mov_eq, ← map_actP] at e
    let F : B.V i := ⟨_, polyAction_mem_VV (B.lam i) (fun τ =>
        gm R w ((B.ch.fm.tauOf w).symm τ)
          (Matrix.GeneralLinearGroup.map (R.iK _).toRingHom (g ((B.ch.fm.tauOf w).symm τ))))
        (mem_VV_of_locP _ _ hz₀)⟩
    exact ⟨F, (key g (fun v => (frame_iff R v _ L (hs v) _).1 (hh v)) F).2 ⟨z₀, hz₀, rfl⟩, (co_eq_iff R y F).1 e⟩
  · rintro ⟨F, hF, e⟩
    choose g hg using fun v : B.ch.A.vT => basisAtEx B.E _ L hL (B.pr v).1
    obtain ⟨z₀, hz₀, hFz⟩ := (key g hg F).1 hF
    refine ⟨fun v => Matrix.GeneralLinearGroup.map (R.iK v).toRingHom (g v),
      fun v => (frame_iff R v _ L (hs v) _).2 (hg v), _, (mem_intSpan_iff D w _ _ (natW_lam B i) _).2 ⟨z₀, hz₀, rfl⟩, ?_⟩
    rw [mov_eq, ← map_actP, ← hFz]
    exact (co_eq_iff R y F).2 e

theorem ker_iff (b) (d : (B.I.S i).D b) (v : B.ch.A.vT) (x : Fin (D.R.N i) → B.E) :
    (fun a => R.iK v (x a)) ∈ ((R.pt b d).2 v).ker ↔ x ∈ localization₂ (B.pr v).1.asIdeal ((B.J.A i).deco b d).L := by
  rw [((B.hJ.tied i).ok b d).mem_locP_L]
  refine and_congr (R.pt_L b d v x) ?_
  have := R.pt_f b d v x
  exact ⟨fun h => this.symm.trans h, fun h => this.trans h⟩

theorem valIs (hS : B.Sees) : R.ValIs (coord R hS) where
  dual w hw b d y := by
    have hd := (B.hJ.tied i).ok b d
    obtain ⟨a, ha⟩ := exists_sepElt sp.nonconj
    by_cases hs : B.Z.seenP w = true
    · have := valB_iff R hS hw ∅ (R.pt b d) hd.Lsh_lattice (fun v x => by
        rw [if_pos ⟨hs, Finset.notMem_empty v⟩, hd.locP_Lsh ha (B.pr v)]
        exact R.pt_L b d v x) y
      rw [if_pos hs] at this
      rw [(B.hJ.tied i).Lsh_eq]
      exact this
    · have := valB_iff R hS hw ∅ (R.pt b d) hd.L_lattice (fun v x => by
        rw [if_neg fun h => hs h.1]
        exact ker_iff R b d v x) y
      rw [if_neg hs] at this
      rw [(B.hJ.tied i).Lsh_eq]
      exact this
  ker w hw hs b d y := by
    have := valB_iff R hS hw Finset.univ (R.pt b d) ((B.hJ.tied i).ok b d).L_lattice (fun v x => by
      rw [if_neg fun h => h.2 (Finset.mem_univ v)]
      exact ker_iff R b d v x) y
    rw [if_pos hs] at this
    exact this

theorem valB_single (hS : B.Sees) {w : D.what₂.places.Pl} (hw : OverT B.ch w) (hs : B.Z.seenP w = true) (v : B.ch.A.vT) (b)
    (d : (B.I.S i).D b) (y : M.Val) :
    y ∈ (coord R hS).valB w {v} (R.pt b d) ↔ y ∈ wl M w ((B.J.A i).ker b d (B.pr v)) := by
  have hd := (B.hJ.tied i).ok b d
  obtain ⟨a, ha⟩ := exists_sepElt sp.nonconj
  have := valB_iff R hS hw {v} (R.pt b d) (hd.LshKer_lattice ha (B.pr v)) (fun v' x => by
    by_cases h : v' = v
    · subst h
      rw [if_neg fun h => h.2 (Finset.mem_singleton_self _), hd.locP_LshKer_self ha, localization_kerAt_eq hd]
      exact ker_iff R b d v' x
    · rw [if_pos ⟨hs, fun h' => h (Finset.mem_singleton.1 h')⟩, hd.locP_LshKer_ne ha (P := B.pr v) (Q := B.pr v') h,
        hd.locP_Lsh ha (B.pr v')]
      exact R.pt_L b d v' x) y
  rw [if_pos hs] at this
  rw [(B.hJ.tied i).ker_eq]
  exact this

theorem ev_rho (b) (g : (B.I.S i).G b) (F : B.V i) :
    B.ev i ((B.I.S i).rho B.emb (B.lam i) b g F) = (B.I.S i).tr B.emb D.what₂.embLL b g (B.ev i F) :=
  GlobalTheory.LvT.BuiltChain.evV_rho B.emb D.what₂.embLL (B.I.S i) (B.lam i) b g F

theorem forms_iff (w : D.what₂.places.Pl) (L : (B.I.S i).Cl → Submodule (𝓞 B.E) (Fin (D.R.N i) → B.E))
    (φ : (B.I.S i).Cl → Fr B.emb D.what₂.embLL (D.R.N i) → ℂ) (hφ : φ ∈ (B.I.S i).Fi B.emb D.what₂.embLL (B.lam i)) :
    (∃ x ∈ locW D.what₂.places w ((B.I.S i).latOf B.emb (B.lam i) (B.lf.fam i) fun c => delAtr B.emb (B.lam i) (L c)),
      (B.I.S i).embF B.emb D.what₂.embLL (B.lam i) (B.lf.fam i) x = φ) ↔
    ∀ c, ∃ F ∈ B.valAt w i (L c), φ c = B.ev i F := by
  classical
  constructor
  · rintro ⟨x, hx, rfl⟩ c
    obtain ⟨s, hs, hx⟩ := (D.mem_locW_iff w _ _).1 hx
    exact ⟨x.1 c, (lc_mem_locP _ _ _).2 ⟨s, hs, hx c⟩, rfl⟩
  · intro h
    choose F hF hφF using h
    let := B.I.clFin B.hI i
    let x : (B.I.S i).FormsK B.emb (B.lam i) (B.lf.fam i) := ⟨F, fun c γ => by
      apply evV_injective B.emb 1 (B.lam i) D.what₂.embLL (fr0 B.emb D.what₂.embLL _)
      have h1 := (hφ c).2 γ
      rw [hφF c, ← ev_rho] at h1
      exact h1⟩
    refine ⟨x, (D.mem_locW_iff w _ _).2 ?_, funext fun c => (hφF c).symm⟩
    choose s hs hsm using fun c => (lc_mem_locP _ _ _).1 (hF c)
    refine ⟨∏ c, s c, fun hm => ?_, fun c => ?_⟩
    · obtain ⟨c, -, hc⟩ := (Ideal.IsPrime.prod_mem_iff (hp := (D.plEq w).isPrime)).1 hm
      exact hs c hc
    · have e : (∏ c, s c) = (∏ c' ∈ Finset.univ.erase c, s c') * s c := by
        rw [mul_comm, Finset.mul_prod_erase _ _ (Finset.mem_univ c)]
      change (∏ c, s c) • F c ∈ _
      rw [e]
      exact (mul_smul _ (s c) (F c)).symm ▸ (delAtr B.emb (B.lam i) (L c)).smul_mem _ (hsm c)

include R in
theorem valIn_iff (w : D.what₂.places.Pl) (L : (B.I.S i).Cl → Submodule (𝓞 B.E) (Fin (D.R.N i) → B.E))
    (W : M.Pt → Set M.Val) (hW : ∀ c y, y ∈ W (R.pt c.1 ((B.I.S i).rep c)) ↔ y ∈ wl M w (L c)) (φ : Fn B.ch i) :
    (∀ c, ∃ F ∈ B.valAt w i (L c), φ c = B.ev i F) ↔ M.ValIn W φ := by
  refine forall_congr' fun c => ?_
  replace hW : ∀ y, y ∈ W (M.rep c) ↔ y ∈ wl M w (L c) := fun y => (R.rep_eq c).symm ▸ hW c y
  constructor
  · rintro ⟨F, hF, e⟩
    have hm : B.ev i F ∈ M.Val := by
      rw [R.val_eq]
      exact evV_mem_ValC B.emb 1 _ D.what₂.embLL F
    exact ⟨⟨_, hm⟩, (hW _).2 ⟨F, hF, rfl⟩, e⟩
  · rintro ⟨y, hy, e⟩
    obtain ⟨F, hF, e'⟩ := (hW y).1 hy
    exact ⟨F, hF, e.trans e'⟩

theorem wl_hom (w : D.what₂.places.Pl) (b) (g : (B.I.S i).G b) (d : (B.I.S i).D b) {y : M.Val}
    (hy : y ∈ wl M w ((B.I.S i).Lsh b d)) : M.act (R.hom b g) y ∈ wl M w ((B.I.S i).Lsh b (g • d)) := by
  obtain ⟨F, hF, e⟩ := hy
  refine ⟨(B.I.S i).rho B.emb (B.lam i) b g F, ?_, by rw [R.act_hom, ev_rho, e]⟩
  obtain ⟨s, hs, hF⟩ := (lc_mem_locP _ _ _).1 hF
  refine (lc_mem_locP _ _ _).2 ⟨s, hs, ?_⟩
  have h : delAtr B.emb (B.lam i) ((B.I.S i).Lsh b (g • d)) = (delAtr B.emb (B.lam i) ((B.I.S i).Lsh b d)).map
      (((B.I.S i).rho B.emb (B.lam i) b g).restrictScalars (𝓞 D.what₂.LL)) := (B.lf.fam i b).del_smul g d
  rw [h]
  exact ⟨_, hF, LinearMap.map_smul_of_tower _ _ _⟩

theorem wl_zeta (w : D.what₂.places.Pl) (L : Submodule (𝓞 B.E) (Fin (D.R.N i) → B.E)) (ζ) {y : M.Val}
    (hy : y ∈ wl M w L) : M.act (R.zeta ζ) y ∈ wl M w L := by
  obtain ⟨F, hF, e⟩ := hy
  refine ⟨((ζ.1 : (D.what₂.LL)ˣ) : D.what₂.LL) • F, ?_, ?_⟩
  · exact (B.valAt w i _).smul_mem (⟨_, BarPass.isIntegral_torsion ζ⟩ : 𝓞 D.what₂.LL) hF
  · rw [R.act_zeta, BarPass.ev_smul, ← e]
    rfl

theorem woff_pt {w : D.what₂.places.Pl} (hw : ¬ OverT B.ch w) (b) (d : (B.I.S i).D b) (y : M.Val) :
    y ∈ woff R w (R.pt b d).1 ↔ y ∈ wl M w ((B.I.S i).Lsh b d) := by
  rw [mem_woff]
  constructor
  · intro h
    have := h 1 b d (by rw [one_smul])
    rwa [inv_one, map_one, Module.End.one_apply] at this
  · intro hy g b' d' h
    obtain ⟨ζ, g', rfl⟩ := R.gen b' g
    rw [mul_smul, ← R.pt_smul] at h
    obtain rfl := R.idx _ _ _ _ _ h
    obtain ⟨k, hk, -, hr⟩ := (R.fst _ _ _ _).1 h
    have hT : ((B.J.T : ℕ) : 𝓞 D.what₂.LL) ∉ (D.plEq w).asIdeal := fun hm =>
      hw (GlobalTheory.LvT.Inh.resChar_eq_of_mem_plEq D w B.hJ.T_prime hm)
    have e1 : (B.I.S i).Lsh b' (k • g' • d') = (B.I.S i).Lsh b' (g' • d') := by
      ext x
      have := (B.hI.step i).lsh_smul b' k (g' • d') x
      rwa [hk, Units.val_one, Matrix.one_mulVec] at this
    have e2 : B.valAt w i ((B.I.S i).Lsh b' (g' • d')) = B.valAt w i ((B.I.S i).Lsh b' d) := by
      rw [← e1, (B.hJ.tied i).Lsh_eq, (B.hJ.tied i).Lsh_eq]
      exact delAtr_off B.emb (B.lam i) ((B.hJ.tied i).ok _ _) ((B.hJ.tied i).ok _ _) sp.T_mem (sp.off_lat _ _ _ hr) hT
    have h1 : y ∈ wl M w ((B.I.S i).Lsh b' (g' • d')) := by
      obtain ⟨F, hF, e⟩ := hy
      exact ⟨F, by rw [e2]; exact hF, e⟩
    have h2 := wl_hom R w b' g'⁻¹ _ (wl_zeta R w _ ζ⁻¹ h1)
    rwa [inv_smul_smul, ← Module.End.mul_apply, ← map_mul, map_inv, map_inv, ← _root_.mul_inv_rev] at h2

theorem woff_act (w : D.what₂.places.Pl) (g : M.G) (p : M.Pt) (y : M.Val) (hy : y ∈ woff R w p.1) :
    M.act g y ∈ woff R w (g • p).1 := by
  rw [mem_woff] at hy ⊢
  intro h b d e
  have h1 := M.smul_fst g⁻¹ _ _ e
  rw [inv_smul_smul, ← mul_smul] at h1
  have h2 := hy _ b d h1
  rwa [_root_.mul_inv_rev, inv_inv, map_mul, Module.End.mul_apply] at h2

theorem gm_unit (w : D.what₂.places.Pl) {γ : GL (Fin (D.R.N i)) B.E} (hγ : γ.valᴴ * γ.val = 1) (τ : D.what₂.Tau) :
    Formalism.UG.bc D.what₂.embLL (gm R w ((B.ch.fm.tauOf w).symm τ) (Matrix.GeneralLinearGroup.map (R.iK _).toRingHom γ)) =
      invTrK (embGL (embAt D.what₂.embLL B.emb) γ) τ := by
  have e : B.Z.tauOf w (B.pr ((B.ch.fm.tauOf w).symm τ)) = τ := (B.Z.tauOf w).apply_symm_apply τ
  rw [gm_iK, e]
  split_ifs
  · exact Units.ext rfl
  · have h2 : (γ⁻¹).val = _ := Units.inv_eq_of_mul_eq_one_left hγ
    refine Units.ext (Matrix.ext fun a c => ?_)
    show _ = D.what₂.embLL (B.emb τ ((γ⁻¹).val c a))
    rw [h2]
    rfl

theorem coord_ok (hS : B.Sees) : (coord R hS).Ok where
  act_co w _ g := by
    obtain ⟨γ, ζ, hγ, hl, ha⟩ := R.rat g
    obtain ⟨k, hk, h⟩ := (isOfFinOrder_iff_pow_eq_one).1 ((CommGroup.mem_torsion _).1 ζ.2)
    refine ⟨((ζ.1 : (D.what₂.LL)ˣ) : D.what₂.LL), k, hk, by rw [← Units.val_pow_eq_pow_val, h, Units.val_one], fun y => ?_⟩
    obtain ⟨F, hF⟩ := exists_pol R y
    have h1 := GlobalTheory.TilClass.trFr_fnOf B.emb D.what₂.embLL (B.lam i) γ ζ.1 F
    rw [← hF, ← map_smul] at h1
    have h2 : co M (M.act g y) = _ := co_of_eq ((ha y).trans h1)
    have h3 : co M y = _ := co_of_eq hF
    show co M (M.act g y) = _ • (coord R hS).mov w (fun v => M.loc v g) (co M y)
    rw [h2, h3, mov_eq]
    simp only [hl, gm_unit R w hγ]
    rfl
  S_on w hw φ hφ :=
    (forms_iff w (fun c => (B.I.S i).Lsh c.1 ((B.I.S i).rep c)) φ hφ).trans
      (valIn_iff R w _ _ (fun c y => (valIs R hS).dual w hw c.1 _ y) φ)
  B_on w hw hs v φ hφ :=
    (forms_iff w (fun c => (B.J.A i).ker c.1 ((B.I.S i).rep c) (B.pr v)) φ hφ).trans
      (valIn_iff R w _ _ (fun c y => valB_single R hS hw hs v c.1 _ y) φ)
  off_act w _ g p y := ⟨fun h => by
    have := woff_act R w g⁻¹ (g • p) _ h
    rwa [inv_smul_smul, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at this,
    woff_act R w g p y⟩
  S_off w hw φ hφ :=
    (forms_iff w (fun c => (B.I.S i).Lsh c.1 ((B.I.S i).rep c)) φ hφ).trans
      (valIn_iff R w _ (fun p => (woff R w p.1 : Set M.Val)) (fun c y => woff_pt R hw c.1 _ y) φ)

theorem exists_coord : ∀ (D : D7) (u : D.what₂.Word) (B : Built.Dat D u) (i : ℕ) (sp : Split (B.J.A i) B.J.T) (M : PtModel B.ch i) (R : B.Real i sp M), i ≤ D.R.m → B.Sees → ∃ Co : M.Coord, Co.Ok ∧ R.ValIs Co :=
  fun _ _ _ _ _ _ R _ hS => ⟨coord R hS, coord_ok R hS, valIs R hS⟩

end GlobalTheory.LvT.Built.ValLat
