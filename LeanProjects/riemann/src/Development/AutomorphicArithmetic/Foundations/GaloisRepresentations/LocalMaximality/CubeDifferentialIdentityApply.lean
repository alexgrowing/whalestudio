import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.DualForm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.PWdBasic
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

private theorem acx_off {σ E : Type} [LinearOrder σ] [AddCommGroup E] [Module ℂ E]
    (A : Finset σ → Submodule ℂ E) (w : σ → Module.End ℂ E) (n : ℤ) (c : Finset σ → E)
    (hc : c ∈ (acx A w).C n) (s : Finset σ) (hs : (s.card : ℤ) ≠ n) : c s = 0 := by
  have hc' : c ∈ Submodule.pi Set.univ (fun s : Finset σ => if (s.card : ℤ) = n then A s else ⊥) := hc
  have h := (Submodule.mem_pi.1 hc') s (Set.mem_univ s)
  rw [if_neg hs] at h
  simpa using h

private theorem acx_on {σ E : Type} [LinearOrder σ] [AddCommGroup E] [Module ℂ E]
    (A : Finset σ → Submodule ℂ E) (w : σ → Module.End ℂ E) (n : ℤ) (c : Finset σ → E)
    (hc : c ∈ (acx A w).C n) (s : Finset σ) (hs : (s.card : ℤ) = n) : c s ∈ A s := by
  have hc' : c ∈ Submodule.pi Set.univ (fun s : Finset σ => if (s.card : ℤ) = n then A s else ⊥) := hc
  have h := (Submodule.mem_pi.1 hc') s (Set.mem_univ s)
  rwa [if_pos hs] at h

private theorem cubeDifferential_identity_apply {σ E : Type} [LinearOrder σ] [AddCommGroup E] [Module ℂ E]
    (c : Finset σ → E) (t : Finset σ) :
    wd (fun _ => (1 : Module.End ℂ E)) c t = ∑ i ∈ t, (GlobalTheory.cubeSign t i : ℤ) • c (t.erase i) := by
  simp [wd, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply]

private theorem pk_mem {d : ℕ} {I : Finset (Fin (d + 1))} (h : I.Nonempty) : pk I ∈ I := by
  unfold pk
  rw [dif_pos h]
  exact I.min'_mem h

section
variable {d : ℕ} {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E] (T : Sys d S E)
  {κ : Type} [LinearOrder κ] [Fintype κ] (n : κ → ℕ × ℕ) (z : κ → S)

private theorem col_KE (hRS : RS) (hKS : KSub) (hOk : SysOk) (hG : T.Good) (hAd : T.admitted n z)
    (I J : Finset (Fin (d + 1))) (hI : I.Nonempty) (hJ : J.Nonempty) (e : Fin d ↪o κ)
    (h : KE (kos T.act (T.M I J) fun l => T.r n z (pk I) (pk J) (e l)) d) :
    KE (T.colCx n z I J) d := by
  have hr := ((hOk d S E T κ n z hG hAd).2.1 I J (pk I) (pk_mem hI) (pk J) (pk_mem hJ)).1
  have hk := (hKS S E T.act κ (T.R I J) (T.M I J) (T.r n z (pk I) (pk J)) (hG.stab I J hI hJ) hr).1 d e h
  intro m hm x hx
  have hR := hRS S E T.act κ (T.M I J) (T.u n (pk I) (pk J)) (T.r n z (pk I) (pk J)) z (fun _ => rfl) m x
  exact hR.2.2.1.2 (hk m hm (hR.2.1.1 hx))

private theorem col_B (hRS : RS) (hKS : KSub) (hK2 : KoszulBoundaryOfComponentMemIdeal) (hOk : SysOk) (hG : T.Good) (hAd : T.admitted n z)
    (I J : Finset (Fin (d + 1))) (hI : I.Nonempty) (hJ : J.Nonempty) (e : Fin d ↪o κ)
    (h : KE (kos T.act (T.M I J) fun l => T.r n z (pk I) (pk J) (e l)) d)
    (x : Finset κ → E) (hx : x ∈ (T.colCx n z I J).Z d)
    (hm : unsc T.act (T.u n (pk I) (pk J)) x (img e) ∈
      sm T.act (T.M I J) (Set.range fun j => T.r n z (pk I) (pk J) (e j))) :
    x ∈ (T.colCx n z I J).B d := by
  have hr := ((hOk d S E T κ n z hG hAd).2.1 I J (pk I) (pk_mem hI) (pk J) (pk_mem hJ)).1
  have hR := hRS S E T.act κ (T.M I J) (T.u n (pk I) (pk J)) (T.r n z (pk I) (pk J)) z (fun _ => rfl) d x
  exact hR.2.2.1.2 (hK2 S E T.act κ (T.R I J) (T.M I J) (T.r n z (pk I) (pk J)) d e (hG.stab I J hI hJ) hr h _
    (hR.2.1.1 hx) hm)

private theorem core (hU : WdUni) (hW : WdBasic) (hB : SysBasic) (hOk : SysOk) (hL1 : CechKoszulSystemBoundaryCriterion)
    (hG : T.Good) (hAd : T.admitted n z)
    (hK : ∀ I J, I.Nonempty → J.Nonempty → KE (T.colCx n z I J) d) (p : ℕ)
    (c : Finset (Two d ⊕ₗ κ) → E) (hc : c ∈ (T.cx n z).Z ((d : ℤ) + p + 2))
    (hlev : ∀ (b : Finset (Two d)) (L : Finset κ), d < L.card → c (uni b L) = 0)
    (Y : Finset (Two d) → Finset κ → E)
    (hY : ∀ b, Y b = 0 ∨ ((lft b).Nonempty ∧ (rgt b).Nonempty ∧ b.card = p + 1 ∧
      Y b ∈ (T.colCx n z (lft b) (rgt b)).Z d))
    (hfin : ∀ I J : Finset (Fin (d + 1)), I.Nonempty → J.Nonempty → I.card + J.card = p + 2 →
      ∀ e ∈ (T.colCx n z I J).Z d,
        (∀ L, e L = c (uni (uni I J) L) - wd (fun _ => (1 : Module.End ℂ E)) (fun b' => Y b' L) (uni I J)) →
        e ∈ (T.colCx n z I J).B d) :
    c ∈ (T.cx n z).B ((d : ℤ) + p + 2) := by
  have hl : ∀ (b : Finset (Two d)) (L : Finset κ), lft (uni b L) = b := fun b L =>
    (hU (Two d) κ E (fun _ => 0) (fun _ => 0) b L).2.1
  have hr : ∀ (b : Finset (Two d)) (L : Finset κ), rgt (uni b L) = L := fun b L =>
    (hU (Two d) κ E (fun _ => 0) (fun _ => 0) b L).2.2.1
  have hl2 : ∀ I J : Finset (Fin (d + 1)), lft (uni I J) = I := fun I J =>
    (hU (Fin (d + 1)) (Fin (d + 1)) E (fun _ => 0) (fun _ => 0) I J).2.1
  have hr2 : ∀ I J : Finset (Fin (d + 1)), rgt (uni I J) = J := fun I J =>
    (hU (Fin (d + 1)) (Fin (d + 1)) E (fun _ => 0) (fun _ => 0) I J).2.2.1
  have hcard : ∀ I J : Finset (Fin (d + 1)), (uni I J).card = I.card + J.card := fun I J =>
    (hU (Fin (d + 1)) (Fin (d + 1)) E (fun _ => 0) (fun _ => 0) I J).2.2.2.1
  obtain ⟨N, hN⟩ : ∃ N : ℤ, N = (d : ℤ) + p + 2 := ⟨_, rfl⟩
  rw [← hN] at hc ⊢
  let y : Finset (Two d ⊕ₗ κ) → E := fun s => Y (lft s) (rgt s)
  have hyu : ∀ b L, y (uni b L) = Y b L := fun b L => by simp only [y, hl, hr]
  have hYs : ∀ b L, L.card ≠ d → Y b L = 0 := by
    intro b L hL
    rcases hY b with h | ⟨_, _, _, h⟩
    · rw [h]; rfl
    · exact acx_off _ _ d (Y b) h.1 L (by exact_mod_cast hL)
  have hYz : ∀ b, wd (fun l => T.wt z (inrE l)) (Y b) = 0 := by
    intro b
    rcases hY b with h | ⟨_, _, _, h⟩
    · rw [h, map_zero]
    · exact h.2
  have hyC : y ∈ (T.cx n z).C (N - 1) := by
    refine ((hB d S E T κ n z (N - 1)).2.1 y).2 fun I J => ?_
    have hcolE : col y (uni I J) = Y (uni I J) := by
      funext L
      exact hyu _ _
    rw [hcolE]
    rcases hY (uni I J) with h | ⟨h1, h2, h3, h4⟩
    · rw [h]
      exact Submodule.zero_mem _
    · rw [hl2] at h1
      rw [hr2] at h2
      rw [hl2, hr2] at h4
      rw [hcard] at h3
      rw [if_pos ⟨h1, h2⟩]
      have e1 : N - 1 - (I.card : ℤ) - J.card = d := by
        have : (I.card : ℤ) + J.card = p + 1 := by exact_mod_cast h3
        omega
      rw [e1]
      exact h4.1
  have hIs := (hW _ E _ (T.wt z)).2.1 (hOk d S E T κ n z hG hAd).1 (N - 1) y hyC
  have hDy : wd (T.wt z) y ∈ (T.cx n z).Z N := by
    refine ⟨?_, ?_⟩
    · have := hIs.1
      rwa [sub_add_cancel] at this
    · exact hIs.2
  have hval : ∀ b L, (c - wd (T.wt z) y) (uni b L) =
      c (uni b L) - wd (fun _ => (1 : Module.End ℂ E)) (fun b' => Y b' L) b := by
    intro b L
    have h1 := (hU (Two d) κ E (T.wt z) y b L).1
    have h2 : (fun L' => y (uni b L')) = Y b := by
      funext L'
      exact hyu _ _
    have h3 : (fun b' => y (uni b' L)) = fun b' => Y b' L := by
      funext b'
      exact hyu _ _
    rw [h2, h3, hYz b, Pi.zero_apply, smul_zero, add_zero] at h1
    rw [Pi.sub_apply, h1]
    rfl
  have hc' : c - wd (T.wt z) y ∈ (T.cx n z).Z N := Submodule.sub_mem _ hc hDy
  have hlev' : ∀ (b : Finset (Two d)) (L : Finset κ), d < L.card → (c - wd (T.wt z) y) (uni b L) = 0 := by
    intro b L hL
    have h0 : (fun b' => Y b' L) = 0 := by
      funext b'
      exact hYs b' L hL.ne'
    rw [hval, hlev b L hL, h0, map_zero]
    simp
  have hcols : ∀ I J : Finset (Fin (d + 1)), I.Nonempty → J.Nonempty → ((I.card + J.card : ℕ) : ℤ) = N - d →
      col (c - wd (T.wt z) y) (uni I J) ∈ (T.colCx n z I J).B d := by
    intro I J hI hJ hIJ
    have hcard2 : I.card + J.card = p + 2 := by
      have : ((I.card + J.card : ℕ) : ℤ) = ((p + 2 : ℕ) : ℤ) := by
        rw [hIJ, hN]
        push_cast
        ring
      exact_mod_cast this
    have hZ := (hB d S E T κ n z N).2.2.2.2.1 _ hc' I J hI hJ (fun I' J' L hlt => by
      by_cases hL : d < L.card
      · exact hlev' _ L hL
      · refine (hB d S E T κ n z N).1 _ hc'.1 I' J' L (Or.inr (Or.inr ?_))
        have h1 : ((I'.card + J'.card + L.card : ℕ) : ℤ) < ((d + p + 2 : ℕ) : ℤ) := by
          have : I'.card + J'.card + L.card < d + p + 2 := by omega
          exact_mod_cast this
        rw [hN]
        push_cast at h1 ⊢
        omega)
    have e1 : N - (I.card : ℤ) - J.card = d := by
      push_cast at hIJ
      omega
    rw [e1] at hZ
    exact hfin I J hI hJ hcard2 _ hZ fun L => hval _ L
  have hfinal := hL1 d S E T κ n z N hG hAd hK _ hc' hlev' hcols
  have hsum : c = (c - wd (T.wt z) y) + wd (T.wt z) y := by abel
  rw [hsum]
  exact Submodule.add_mem _ hfinal (Submodule.mem_map_of_mem hyC)

end

theorem UpperTheory.Gal.productCup_of_system.pCmp_of :
    PLift → ColP → CechKoszulSystemBoundaryCriterion → SysBasic → SysOk → KoszulBoundaryOfComponentMemIdeal → KSub → RS → GoodZ → ThMuLat → MuSpan → ActsLin → WdUni → PCmp := by
  intro hLift hColP hL1 hB hOk hK2 hKS hRS hGood hThLat _ hAct hU F K _ _ _ _ _ _ d x hx a p c hc hlev γ hγ hval
  obtain ⟨τ, hτ⟩ := hx.exists_isTop
  have hG : (sysP K x a).Good := (hGood F K d x hx a).2.1
  have hAd := (hThLat d _ _ (sysP K x a) hG).1
  obtain ⟨γ', hγ', rfl⟩ := hγ
  have hex : ∀ b : Finset (Two d), ∃ yb : Finset (Mi d) → F ⊗[ℂ] DR ℂ K,
      (yb = 0 ∨ ((lft b).Nonempty ∧ (rgt b).Nonempty ∧ b.card = p + 1 ∧
        yb ∈ ((sysP K x a).colCx n11 (sysP K x a).mu (lft b) (rgt b)).Z d)) ∧
      ∀ L : Finset (Mi d), L.card = d → mulP F K (yb L) = kap K x L • γ' b := by
    intro b
    by_cases h : (lft b).Nonempty ∧ (rgt b).Nonempty ∧ b.card = p + 1
    · have hm := acx_on _ _ _ γ' hγ' b (by rw [h.2.2]; push_cast; ring)
      have hm' : γ' b ∈ omB ℂ K (rB ℂ K (xv x) (lft b ∪ rgt b)) a := by
        simpa only [mixF, if_pos (And.intro h.1 h.2.1)] using hm
      obtain ⟨yb, h1, h2⟩ := hLift F K d x hx a (lft b) (rgt b) h.1 h.2.1 _ hm'
      exact ⟨yb, Or.inr ⟨h.1, h.2.1, h.2.2, h1⟩, h2⟩
    · have h0 : γ' b = 0 := by
        by_cases hb : b.card = p + 1
        · have hm := acx_on _ _ _ γ' hγ' b (by rw [hb]; push_cast; ring)
          have hn : ¬ ((lft b).Nonempty ∧ (rgt b).Nonempty) := fun h' => h ⟨h'.1, h'.2, hb⟩
          simpa only [mixF, if_neg hn, Submodule.mem_bot] using hm
        · exact acx_off _ _ _ γ' hγ' b (by
            intro h'
            apply hb
            have : (b.card : ℤ) = ((p + 1 : ℕ) : ℤ) := by rw [h']; push_cast; ring
            exact_mod_cast this)
      refine ⟨0, Or.inl rfl, fun L _ => ?_⟩
      simp [h0]
  choose Y hY1 hY2 using hex
  have hKE : ∀ I J, I.Nonempty → J.Nonempty → KE ((sysP K x a).colCx n11 (sysP K x a).mu I J) d :=
    fun I J hI hJ => col_KE _ _ _ hRS hKS hOk hG hAd I J hI hJ (dj (pk J))
      (hColP F K d x hx a I J (pk I) (pk_mem hI) (pk J) (pk_mem hJ)).1
  refine core (sysP K x a) n11 (sysP K x a).mu hU wdBasic_of hB hOk hL1 hG hAd hKE p c hc hlev Y hY1 ?_
  intro I J hI hJ _ e he heq
  have hP := hColP F K d x hx a I J (pk I) (pk_mem hI) (pk J) (pk_mem hJ)
  refine col_B _ _ _ hRS hKS hK2 hOk hG hAd I J hI hJ (dj (pk J)) hP.1 e he ?_
  have hR := hRS _ _ (sysP K x a).act (Mi d) ((sysP K x a).M I J) ((sysP K x a).u n11 (pk I) (pk J))
    ((sysP K x a).r n11 (sysP K x a).mu (pk I) (pk J)) (sysP K x a).mu (fun _ => rfl) d e
  have hcardL : (img (dj (d := d) (pk J))).card = d := by simp [img]
  refine hP.2 _ (acx_on _ _ _ _ (hR.2.1.1 he).1 _ (by rw [hcardL])) ?_
  show mulP F K ((sysP K x a).act _ (e _)) = 0
  rw [(hAct F K d x hx τ hτ a).2.2.2.2.1]
  have h0 : mulP F K (e (img (dj (pk J)))) = 0 := by
    have hv : mulP F K (c (uni (uni I J) (img (dj (pk J))))) = kap K x (img (dj (pk J))) •
        wd (fun _ => (1 : Module.End ℂ (DR ℂ K))) γ' (uni I J) := hval _ _ hcardL
    rw [heq, map_sub, hv, sub_eq_zero, cubeDifferential_identity_apply, cubeDifferential_identity_apply, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, hY2 _ _ hcardL, smul_comm]
  rw [h0, smul_zero]
