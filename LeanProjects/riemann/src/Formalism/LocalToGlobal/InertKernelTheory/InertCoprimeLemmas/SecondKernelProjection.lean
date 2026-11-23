import Formalism.LocalToGlobal.InertKernelTheory.ProjRSurj

noncomputable section

namespace Formalism.L2.KerInert.SecondKernelProjection

open Formalism.MainNotions.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG NumberField IsDedekindDomain Matrix Classical

section Sel

variable {K A B : Type} [Field K] [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]

theorem secR_mem (R : Submodule K (A × B)) (a : R.map (LinearMap.fst K A B)) : ((a : A), secR R a) ∈ R := by
  have hs := Classical.choose_spec (LinearMap.exists_rightInverse_of_surjective (projR R)
    (LinearMap.range_eq_top.2 (projR_surj R)))
  set s := Classical.choose (LinearMap.exists_rightInverse_of_surjective (projR R)
    (LinearMap.range_eq_top.2 (projR_surj R))) with hsdef
  have h1 : projR R (s a) = a := LinearMap.congr_fun hs a
  have h2 : ((s a : R) : A × B).1 = (a : A) := congrArg Subtype.val h1
  have h3 : ((a : A), secR R a) = ((s a : R) : A × B) := Prod.ext h2.symm rfl
  rw [h3]
  exact (s a).2

theorem selOf_mem (R : Submodule K (A × B)) (a : A) (ha : a ∈ R.map (LinearMap.fst K A B)) : (a, selOf R a) ∈ R := by
  have hx := Classical.choose_spec (LinearMap.exists_extend (secR R))
  have h1 : selOf R a = secR R ⟨a, ha⟩ := LinearMap.congr_fun hx ⟨a, ha⟩
  rw [h1]
  exact secR_mem R ⟨a, ha⟩

end Sel

section Val

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
  {Tau : Type} [Fintype Tau] {p : ℕ}
  {S : StepLevel F E σ J T f bad} {emb : Tau → E →+* ℂ} {G : GAtP p} {A : LocAt F E n G}
  {pos : (Σ v : Fin G.P.nV, Fin (G.P.n' v)) ≃ Tau}
  {V cls : Type} [AddCommGroup V] [Module ℂ V] {embV : V →ₗ[ℂ] (cls → Frames (gramC J emb) → ℂ)}
  {yc : cls → UPts σ J (FiniteAdeleRing (𝓞 F) F)}

theorem isValV_uniq (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x)) (hi : EvInj emb G A pos (J := J))
    (hp : PtEx S G A yc) {x : V} {i : G.comp} {L : G.P.Tup} {Q Q' : XR G.P ℂ} (hL : G.P.IsLatTup L)
    (h : IsValV S emb G A pos embV yc x i L Q) (h' : IsValV S emb G A pos embV yc x i L Q') : Q = Q' := by
  choose g0 hg0 hLg using hL
  let g : ∀ v, GL (Fin (G.P.m + 1)) (G.P.Qq v) := fun v => ((Matrix.isUnit_iff_isUnit_det _).2 (hg0 v)).unit
  have hg : ∀ v, L v = colSpan (G.P.W v) (g v : Matrix (Fin (G.P.m + 1)) (Fin (G.P.m + 1)) (G.P.Qq v)) := hLg
  obtain ⟨c, γ, κ, hγ, hpt⟩ := hp i g
  have hz : evC G.P A.rk pos (gramC J emb) (crdB emb A.B) (Q - Q') = 0 := by
    funext z
    obtain ⟨z', hz'⟩ := frames_tr emb hc γ hγ z
    rw [map_sub, Pi.sub_apply, h g hg c γ hγ κ hpt z z' hz', h' g hg c γ hγ κ hpt z z' hz', sub_self]
    rfl
  exact sub_eq_zero.1 (hi _ hz)

theorem selOf_relV (hc : ∀ τ x, emb τ (σ x) = starRingEnd ℂ (emb τ x)) (hi : EvInj emb G A pos (J := J))
    (hp : PtEx S G A yc) {x : V} {i : G.comp} {L : G.P.Tup} {Q : XR G.P ℂ} (hL : G.P.IsLatTup L)
    (h : IsValV S emb G A pos embV yc x i L Q) : selOf (relV S emb G A pos embV yc i L) x = Q :=
  isValV_uniq hc hi hp hL (selOf_mem (relV S emb G A pos embV yc i L) x (Submodule.mem_map.2 ⟨(x, Q), h, rfl⟩)) h

end Val

section Step

open Formalism.BasicNotions Formalism.MainNotions.G.CmpJ Formalism.L2.G

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {p : ℕ} {i : ℕ} {hi : i ≤ D.R.m}
  {G : GAtP p}

theorem embN_eq_nrmR (S : StepIn M i hi G) (β : S.Ch) (x : (M.lat i).V) : S.embN β x = nrmR S β (M.emb i x) := rfl

theorem rdS_cmpJ (S : StepIn M i hi G) {Kc : Type} [Field Kc] [iA : Algebra G.Kf Kc] (e : D.what₂.LL →+* G.Kf)
    (H : ∀ β, S.Core e β) (hS : BlockRationalityField) (ι : ℂ →+* Kc)
    (hι : ∀ r : D.what₂.LL, ι (D.what₂.embLL r) = algebraMap G.Kf Kc (e r)) (x : (M.lat i).V) (c' : G.comp) (L : G.P.Tup) :
    MvPolynomial.map (algebraMap G.Kf Kc) (S.cmpJ e x c' L) = rdS S ι c' L (M.emb i x) := by
  have hcmp : S.cmpJ e x c' L = cmpC (S.K (S.eC.symm c').1).lev (embT D) D.what₂.embLL (S.charts.gat (S.eC.symm c').1) e
      (S.loc (S.eC.symm c').1) S.pos (S.embN (S.eC.symm c').1) (S.K (S.eC.symm c').1).y x (S.eC.symm c').2 L := rfl
  rw [hcmp]
  by_cases hL : G.P.IsLatTup L
  · simp only [cmpC, rdS, hL, ↓reduceIte]
    have hH := (H (S.eC.symm c').1).toHyp hS
    have hv := valC_spec hH.ex x (S.eC.symm c').2 L hL
    have hV : IsValV (S.K (S.eC.symm c').1).lev (embT D) (S.charts.gat (S.eC.symm c').1) (S.loc (S.eC.symm c').1) S.pos
        (nrmR S (S.eC.symm c').1) (S.K (S.eC.symm c').1).y (M.emb i x) (S.eC.symm c').2 L
        (MvPolynomial.map D.what₂.embLL (valC (S.K (S.eC.symm c').1).lev (embT D) D.what₂.embLL (S.charts.gat (S.eC.symm c').1)
          (S.loc (S.eC.symm c').1) S.pos (S.embN (S.eC.symm c').1) (S.K (S.eC.symm c').1).y x (S.eC.symm c').2 L)) :=
      hv.2
    have hsel : selOf (relV (S.K (S.eC.symm c').1).lev (embT D) (S.charts.gat (S.eC.symm c').1) (S.loc (S.eC.symm c').1) S.pos
        (nrmR S (S.eC.symm c').1) (S.K (S.eC.symm c').1).y (S.eC.symm c').2 L) (M.emb i x) =
        MvPolynomial.map D.what₂.embLL (valC (S.K (S.eC.symm c').1).lev (embT D) D.what₂.embLL (S.charts.gat (S.eC.symm c').1)
          (S.loc (S.eC.symm c').1) S.pos (S.embN (S.eC.symm c').1) (S.K (S.eC.symm c').1).y x (S.eC.symm c').2 L) :=
      selOf_relV (embT_conj D) (evInj_pf (embT D) _ _ _) hH.ptEx hL hV
    rw [LinearMap.comp_apply]
    show _ = MvPolynomial.map ι (selOf (relV (S.K (S.eC.symm c').1).lev (embT D) (S.charts.gat (S.eC.symm c').1)
      (S.loc (S.eC.symm c').1) S.pos (nrmR S (S.eC.symm c').1) (S.K (S.eC.symm c').1).y (S.eC.symm c').2 L) (M.emb i x))
    have hcomp : (algebraMap G.Kf Kc).comp e = ι.comp D.what₂.embLL := RingHom.ext fun r => (hι r).symm
    rw [hsel, MvPolynomial.map_map, MvPolynomial.map_map, hcomp]
  · simp only [cmpC, rdS, hL, ↓reduceIte, map_zero, LinearMap.zero_apply]

end Step

section Cons

open Formalism.BasicNotions Formalism.MainNotions.G.CmpJ Formalism.L2.G

variable {D : D7} {c : LatCmp D} {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}

theorem trC_heq {C C' : ColumnChain D.R D.what₂.Tau (D.hcW u)} (hC : C = C') (i : ℕ) (φ : C'.cls i → C'.Y i → ℂ)
    (ψ : C.cls i → C.Y i → ℂ) (hφ : HEq φ ψ) : trC hC i φ = ψ := by
  subst hC
  exact eq_of_heq hφ

theorem onChain_ofTw (st : ∀ j (hj : j + 1 ≤ D.R.m), StepIn (Tw.fm u μ) (j + 1) hj (gatJ Lv (j + 1))) :
    OnChain (⟨fun j hj => StepAt.ofTw (st j hj)⟩ : CmpJIn Tw u μ w h Lv) := fun _ _ => rfl

theorem onChain_ofMem (st : ∀ j (hj : j + 1 ≤ D.R.m), StepIn (D.fm u) (j + 1) hj (gatJ Lv (j + 1))) :
    OnChain (⟨fun j hj => StepAt.ofMem (st j hj)⟩ : CmpJIn Tw u D.what₂.mu0 w h Lv) := fun _ _ => (D.memberColumns_twistedChain_base u).symm

theorem rdJ_of_isValV (I : CmpJIn Tw u μ w h Lv) (hC : OnChain I) (H : CmpJHyp c I) (hS : BlockRationalityField) {Kc : Type} [Field Kc]
    (ι : ℂ →+* Kc) (j : ℕ) (hj : j + 1 ≤ D.R.m) (c' : Lv.comp (j + 1)) (L' : (Fl.Pj (j + 1)).Tup) (hL' : (Fl.Pj (j + 1)).IsLatTup L')
    (φ : (D.chTw u μ).cls (j + 1) → (D.chTw u μ).Y (j + 1) → ℂ) (Q : XR (Fl.Pj (j + 1)) ℂ)
    (hQ : IsValV ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm c').1).lev (embT D)
      ((I.at' j hj).st.charts.gat ((I.at' j hj).st.eC.symm c').1) ((I.at' j hj).st.loc ((I.at' j hj).st.eC.symm c').1)
      (I.at' j hj).st.pos (nrmR (I.at' j hj).st ((I.at' j hj).st.eC.symm c').1)
      ((I.at' j hj).st.K ((I.at' j hj).st.eC.symm c').1).y (trC (hC j hj) (j + 1) φ) ((I.at' j hj).st.eC.symm c').2 L' Q) :
    rdJ I hC ι j c' L' φ = MvPolynomial.map ι Q := by
  have hH := ((H.core j hj) ((I.at' j hj).st.eC.symm c').1).toHyp hS
  have hsel := selOf_relV (embT_conj D) (evInj_pf (embT D) _ _ _) hH.ptEx hL' hQ
  unfold rdJ
  rw [dif_pos hj]
  simp only [rdS, hL', ↓reduceIte]
  rw [LinearMap.comp_apply, LinearMap.comp_apply]
  exact congrArg (MvPolynomial.map ι) hsel

end Cons

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.FormalGroupSystem Formalism.L2.G Formalism.MainNotions.G.CmpJ Formalism.L2.KerInert.SecondKernelInstances

theorem series_reading_entries : TieReadJ := by
  intro D L hT Gi Gl Kc0 Dx cX ex u μ w h _ Fl Lv Ch K I H hS Gt hCh hC std vp unif eO eO_spec dG dG_spec om Y ι hι j
    y c' L' _
  unfold rdJ
  by_cases hj : j + 1 ≤ D.R.m
  · rw [dif_pos hj]
    have h1 : (kerAtMu_any K H hS Gt Ch hCh).cmp (j + 1) y =
        (I.at' j hj).st.cmpJ (ex.cmp.embW u w h) ((I.at' j hj).eps.symm y) := kerAtMu_cmpJ_cmp K H hS Gt j hj y
    rw [h1, LinearMap.comp_apply, LinearEquiv.coe_coe]
    have h2 : trC (hC j hj) (j + 1) ((ex.tw.fm u μ).emb (j + 1) y) =
        (I.at' j hj).M.emb (j + 1) ((I.at' j hj).eps.symm y) := by
      apply trC_heq
      have := (I.at' j hj).eps_emb ((I.at' j hj).eps.symm y)
      rwa [LinearEquiv.apply_symm_apply] at this
    rw [h2]
    exact rdS_cmpJ (iA := Y.algKf) (I.at' j hj).st (ex.cmp.embW u w h) (H.core j hj) hS ι hι _ c' L'
  · rw [dif_neg hj]
    have h1 : (kerAtMu_any K H hS Gt Ch hCh).cmp (j + 1) y = 0 := by
      show cmpSJ H hS j y = 0
      unfold cmpSJ
      rw [dif_neg hj]
      rfl
    rw [h1]
    simp

end Formalism.L2.KerInert.SecondKernelProjection
