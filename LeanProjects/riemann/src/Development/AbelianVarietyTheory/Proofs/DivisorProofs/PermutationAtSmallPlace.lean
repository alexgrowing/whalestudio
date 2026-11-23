import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassesAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsLocalVacuumOfIsLatticeVacuumCoprimeLevel

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FramePerm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem perm_of_isDC {G : Type} [Group G] (J : Subgroup G) (x : G) (A : Finset G) (h : Bridge.IsDC J x A) (κ : G)
    (hκ : κ ∈ J) : ∃ σ : Equiv.Perm A, ∀ s : A, ((σ s : A) : G)⁻¹ * κ * s ∈ J := by
  classical
  have hex : ∀ s : A, ∃ a : A, (a : G)⁻¹ * (κ * s) ∈ J := by
    intro s
    obtain ⟨k₁, k₂, hs⟩ := h.1 s s.2
    obtain ⟨a, ⟨ha, haJ⟩, -⟩ := h.2 (κ * s) ⟨⟨κ, hκ⟩ * k₁, k₂, by rw [hs]; simp [mul_assoc]⟩
    exact ⟨⟨a, ha⟩, haJ⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro s s' hss
    have h1 := hf s
    have h2 := hf s'
    rw [hss] at h1
    have h3 : (s : G)⁻¹ * s' ∈ J := by
      have := J.mul_mem (J.inv_mem h1) h2
      simpa [mul_assoc] using this
    obtain ⟨k₁, k₂, hs'⟩ := h.1 s' s'.2
    have hu := (h.2 s' ⟨k₁, k₂, hs'⟩).unique ⟨s.2, h3⟩ ⟨s'.2, by simp [J.one_mem]⟩
    exact Subtype.ext hu
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), fun s => ?_⟩
  simpa [mul_assoc] using hf s

theorem map_ev_eq_one_of_loc : ∀ {D : D7} (V : Formalism.BasicNotions.TH.HSp D) {Pl0 : Type} (pl : Pl0 → Pl D.host.E) (ok : Set Pl0) (i : ok × ℕ) (x : Bridge.Gf V) {l : ℕ} [Fact l.Prime] (inc : D.host.E →+* PadicAlgCl l) (ev : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E →+* PadicAlgCl l), EvOk inc ev → ((l : ℕ) : 𝓞 D.host.E) ∉ (pl i.1.1).asIdeal → isLocEnv V pl ok i x → ((x : GL (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)).val).map ev = 1 := by
  intro D V Pl0 pl ok i x l _ inc ev hev hl hx
  obtain ⟨e, α, he, -, hs, hxα⟩ := hx
  obtain ⟨v, ε, ⟨a, rfl, -, ha⟩, hf, hv⟩ := GlobalTheory.VacLat.place_of_primeIdem (Or.inl ⟨he, rfl⟩)
  have h0 : ev (a ⊗ₜ[D.host.F] 1) = 0 := by
    refine hev.2.2.1 a fun v' hv' => ha v' ?_
    rintro rfl
    apply hl
    rw [← hv] at hv'
    have h1 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((l : ℕ) : 𝓞 D.host.F) ∈ (pl i.1.1).asIdeal := hv'
    rwa [map_natCast] at h1
  have h2 := GlobalTheory.SplitHeckeAdj.map_eq_one_of_supp (ev.comp (Formalism.L2.Theta.finPart D)) (e + Formalism.L2.Theta.cA D e)
    (by rw [hf]; exact h0) (Formalism.L2.Theta.mt V α) hs
  rw [hxα]
  exact h2

theorem chi_move {G : Type} [Group G] (J Lc : Subgroup G) (χ : J →* ℂˣ)
    (l2 : ∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ Lc ∧ k = k₁ * k₂ ∧ ∀ l ∈ Lc, Commute k₂ l)
    (l3 : ∀ k : J, (k : G) ∈ Lc → χ k = 1) (κ κ' : J) (a s : G) (ha : a ∈ Lc) (hs : s ∈ Lc)
    (h : (κ' : G) = a⁻¹ * κ * s) : χ κ' = χ κ := by
  obtain ⟨k₁, h₁, k₂, h₂, hL, hk, hc⟩ := l2 κ κ.2
  have e1 : κ = ⟨k₁, h₁⟩ * ⟨k₂, h₂⟩ := Subtype.ext hk
  have e2 : ((κ' * (⟨k₂, h₂⟩ : J)⁻¹ : J) : G) = a⁻¹ * k₁ * s := by
    show (κ' : G) * k₂⁻¹ = _
    rw [h, hk, mul_assoc a⁻¹, mul_assoc k₁, (hc s hs).eq]; group
  have e3 := l3 (κ' * (⟨k₂, h₂⟩ : J)⁻¹) (e2 ▸ Lc.mul_mem (Lc.mul_mem (Lc.inv_mem ha) hL) hs)
  rw [map_mul, map_inv, mul_inv_eq_one] at e3
  rw [e3, e1, map_mul, l3 ⟨k₁, h₁⟩ hL, one_mul]

set_option maxHeartbeats 1600000 in

theorem levChi_eq_of_loc : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (j : Fin D.R.m) (t : p.P.T) (i : (blk p j t).Pl × ℕ), 1 ≤ i.2 → i.2 ≤ (Vc D j).rank → ∀ (κ κ' : levJ p j t) (a s : Bridge.Gf (Vc D j)), a ∈ hkA p j t i → s ∈ hkA p j t i → (κ' : Bridge.Gf (Vc D j)) = a⁻¹ * κ * s → levChi p j t κ' = levChi p j t κ := by
  intro D L hT Gi Gl Kc Y cX ex Csz p j t i h1 h2 κ κ' a s ha hs h
  have hb := p.charW.base
  have ha' : isLocEnv (Vc D j) p.R.pl (p.P.A3.A.ok t) i a := (p.R.B.L j t).hecke.hA_loc i ⟨h1, h2⟩ a ha
  have hs' : isLocEnv (Vc D j) p.R.pl (p.P.A3.A.ok t) i s := (p.R.B.L j t).hecke.hA_loc i ⟨h1, h2⟩ s hs
  refine hb.fam.tie.elim fun _ x => x.elim fun _ x => x.elim fun _ tie => ?_
  refine (hb.lev.βV j).elim fun c hc => ?_
  rw [one_pow] at hc
  refine ha'.elim fun e x => x.elim fun _ x => ?_
  have he := x.1
  have hsp := (tie.ok t _).1 (show (p.P.A3.A.ok t) × ℕ from i).1.2
  have hl := GlobalTheory.SplitHeckeAdj.local_group (Vc D j) (p.R.βV j) (p.R.ΛV j) (p.R.datVt j t) hc _ e he
    fun PP hP => GlobalTheory.SplitHeckeAdj.off_of_splitOff hsp PP (hP.elim (fun h1 => Or.inl (hb.fam.Sb h1)) Or.inr)
  refine hl.elim fun Lc l => ?_
  have hA : a ∈ Lc := (GlobalTheory.SplitHeckeAdj.loc_supp _ ha' he).elim fun g hg => hg.2 ▸ l.1 g hg.1
  have hS : s ∈ Lc := (GlobalTheory.SplitHeckeAdj.loc_supp _ hs' he).elim fun g hg => hg.2 ▸ l.1 g hg.1
  exact chi_move _ Lc _ l.2.1 l.2.2.1 κ κ' a s hA hS h

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem chi_cancel {K R : Type} [Field K] [CommRing R] (io : K ≃+* ℂ) (emb : R →+* K) (hinj : Function.Injective emb)
    (u u' : Rˣ) (X X' : K) (hXX : X' = X) (hX : X ≠ 0) (c c' : ℂ) (hcc : c' = c) (hc : c ≠ 0)
    (e1 : io (emb u' * X') * c' = 1) (e2 : io (emb u * X) * c = 1) : u' = u := by
  subst hXX hcc
  have e4 := io.injective (mul_right_cancel₀ hc (e1.trans e2.symm))
  exact Units.ext (hinj (mul_right_cancel₀ hX e4))

theorem perm_core (p : PtAt ex Csz) (j : Fin D.R.m) (t : p.P.T) (i : (blk p j t).Pl × ℕ)
    (hR : 1 ≤ i.2 ∧ i.2 ≤ (Vc D j).rank) (κ : levJ p j t) :
    ∃ σ : Equiv.Perm (hkA p j t i), ∀ s : hkA p j t i, ((σ s : hkA p j t i) : Bridge.Gf (Vc D j))⁻¹ * κ * s ∈ levJ p j t := by
  have h : Bridge.IsDC (levJ p j t) ((p.R.B.L j t).hecke.hx i) (hkA p j t i) := (p.R.B.L j t).hecke.hDC i hR
  exact perm_of_isDC (levJ p j t) ((p.R.B.L j t).hecke.hx i) (hkA p j t i) h κ κ.2

theorem perm_gen (p : PtAt ex Csz) (j : Fin D.R.m) (t : p.P.T) {l : ℕ} [Fact l.Prime] {N : ℕ}
    (e0 : D.what₂.LL →+* PadicAlgCl l) (b : Bool) (io : PadicAlgCl l ≃+* ℂ)
    (ev : D.what₂.Tau → ((FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗[D.host.F] D.host.E →+* PadicAlgCl l))
    (bs : D.what₂.Tau → GL (Fin N) (PadicAlgCl l)) (rk : Fin N ≃o Fin (Vc D j).rank) (sh : D.what₂.Tau → ℤ)
    (Lf : IntermediateField ℚ_[l] (PadicAlgCl l))
    (kap : levJ p j t →* (D.what₂.Tau → GL (Fin N) (intR Lf))) (chi : levJ p j t →* (intR Lf)ˣ)
    (hev : ∀ τ, EvOk (incOf D e0 b τ) (ev τ)) (hkap : KapEq p j t ev bs rk kap) (hchi : ChiEq p j t io sh kap chi)
    (i : Ix p j t l N) (κ : levJ p j t) :
    ∃ σ : Equiv.Perm (hkA p j t i.1), ∀ s : hkA p j t i.1, ∃ κ' : levJ p j t,
      (κ : Bridge.Gf (Vc D j)) * (s : Bridge.Gf (Vc D j)) = (σ s : Bridge.Gf (Vc D j)) * κ' ∧ kap κ' = kap κ ∧
        chi κ' = chi κ := by
  have hN : N = (Vc D j).rank := Fin.equiv_iff_eq.mp ⟨rk.toEquiv⟩
  have hR : 1 ≤ i.1.2 ∧ i.1.2 ≤ (Vc D j).rank := ⟨i.2.1, by rw [← hN]; exact i.2.2.1⟩
  have hp := perm_core p j t i.1 hR κ
  refine hp.elim fun σ hσ => ?_
  have hinj : Function.Injective (intEmb Lf) := by
    intro x y hxy
    exact Subtype.ext (Subtype.ext hxy)
  have loc : ∀ y ∈ hkA p j t i.1, ∀ τ,
      ((y : GL (Fin (Vc D j).rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)).val).map (ev τ) = 1 := by
    intro y hy τ
    have hy' : isLocEnv (Vc D j) p.R.pl (p.P.A3.A.ok t) i.1 y := (p.R.B.L j t).hecke.hA_loc i.1 hR y hy
    exact map_ev_eq_one_of_loc (Vc D j) p.R.pl (p.P.A3.A.ok t) i.1 y _ (ev τ) (hev τ) i.2.2.2 hy'
  have key : ∀ (κ' : levJ p j t) (a s : Bridge.Gf (Vc D j)), a ∈ hkA p j t i.1 → s ∈ hkA p j t i.1 →
      (κ' : Bridge.Gf (Vc D j)) = a⁻¹ * κ * s → kap κ' = kap κ ∧ chi κ' = chi κ := by
    intro κ' a s ha hs he
    have hmap : ∀ τ, (((κ' : Bridge.Gf (Vc D j)) : GL (Fin (Vc D j).rank)
        (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)).val).map (ev τ) =
        (((κ : Bridge.Gf (Vc D j)) : GL (Fin (Vc D j).rank)
        (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)).val).map (ev τ) := by
      intro τ
      have ha1 := loc a ha τ
      have hs1 := loc s hs τ
      have ha' : ((((a⁻¹ : Bridge.Gf (Vc D j)) : GL (Fin (Vc D j).rank)
          (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)).val).map (ev τ)) = 1 := by
        have h0 : ((((a⁻¹ : Bridge.Gf (Vc D j)) : GL (Fin (Vc D j).rank)
            (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)).val).map (ev τ)) *
            (((a : GL (Fin (Vc D j).rank)
            (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)).val).map (ev τ)) = 1 := by
          rw [← Matrix.map_mul, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one,
            Matrix.map_one _ (ev τ).map_zero (ev τ).map_one]
        rwa [ha1, mul_one] at h0
      rw [he]
      simp only [Subgroup.coe_mul, Units.val_mul, Matrix.map_mul, ha', hs1, one_mul, mul_one]
    have hmat : ∀ τ, kapMat p j t ev bs rk κ' τ = kapMat p j t ev bs rk κ τ := by
      intro τ
      unfold kapMat matOf
      rw [hmap τ]
    have hK : kap κ' = kap κ := by
      funext τ
      apply Units.ext
      apply Matrix.ext
      intro a c
      apply hinj
      have h1 := (hkap κ' τ).trans ((hmat τ).trans (hkap κ τ).symm)
      exact congrFun (congrFun h1 a) c
    refine ⟨hK, ?_⟩
    have hL := levChi_eq_of_loc p j t i.1 hR.1 hR.2 κ κ' a s ha hs he
    have hX : (∏ τ, intEmb Lf (kap κ τ).val.det ^ sh τ) ≠ 0 := by
      refine Finset.prod_ne_zero_iff.mpr fun τ _ => zpow_ne_zero _ ?_
      exact ((Matrix.GeneralLinearGroup.det (kap κ τ)).isUnit.map (intEmb Lf)).ne_zero
    have hXX : (∏ τ, intEmb Lf (kap κ' τ).val.det ^ sh τ) = ∏ τ, intEmb Lf (kap κ τ).val.det ^ sh τ :=
      congrArg (fun f : D.what₂.Tau → GL (Fin N) (intR Lf) => ∏ τ, intEmb Lf (f τ).val.det ^ sh τ) hK
    have hcc : ((levChi p j t κ' : ℂˣ) : ℂ) = ((levChi p j t κ : ℂˣ) : ℂ) := congrArg (fun z : ℂˣ => (z : ℂ)) hL
    have e1 : io (intEmb Lf (chi κ') * ∏ τ, intEmb Lf (kap κ' τ).val.det ^ sh τ) * ((levChi p j t κ' : ℂˣ) : ℂ) = 1 :=
      hchi κ'
    have e2 : io (intEmb Lf (chi κ) * ∏ τ, intEmb Lf (kap κ τ).val.det ^ sh τ) * ((levChi p j t κ : ℂˣ) : ℂ) = 1 :=
      hchi κ
    exact chi_cancel io (intEmb Lf) hinj (chi κ) (chi κ') (∏ τ, intEmb Lf (kap κ τ).val.det ^ sh τ)
      (∏ τ, intEmb Lf (kap κ' τ).val.det ^ sh τ) hXX hX ((levChi p j t κ : ℂˣ) : ℂ) ((levChi p j t κ' : ℂˣ) : ℂ) hcc
      (levChi p j t κ).ne_zero e1 e2
  refine ⟨σ, fun s => ⟨⟨((σ s : hkA p j t i.1) : Bridge.Gf (Vc D j))⁻¹ * κ * s, hσ s⟩, ?_, ?_, ?_⟩⟩
  · show (κ : Bridge.Gf (Vc D j)) * s = (σ s : Bridge.Gf (Vc D j)) * ((σ s : Bridge.Gf (Vc D j))⁻¹ * κ * s)
    group
  · exact (key _ _ _ (σ s).2 s.2 rfl).1
  · exact (key _ _ _ (σ s).2 s.2 rfl).2

set_option maxHeartbeats 800000 in
open Classical in

theorem permAt (p : PtAt ex Csz) (j : Fin D.R.m) (P : Formalism.CohomologicalDescent.LogSmallConstantBounds.Par) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) :
    PermAt p j P w := by
  intro _ e0 b io ev bs rk sh Lf _ kap chi hC
  obtain ⟨-, -, -, hev, hkap, hchi⟩ := hC
  dsimp only [GlobalTheory.FrameOf.frameOf]
  intro i κ
  exact perm_gen p j (p.R.mu w) e0 b io ev bs rk sh Lf kap chi hev hkap hchi i κ

end Point

theorem permSt : InRange fun _ _ _ _ p j P _ w => SmallAt p j P w → PermAt p j P w := by
  unfold InRange AtPts
  exact ⟨1, one_pos, fun eps _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm CH _ _ => ⟨0, fun x hx _ i p _ _ j P W _ _ w _ _ _ => permAt p j P w⟩⟩⟩

end GlobalTheory.FramePerm
