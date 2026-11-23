import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LatticeBlockClasses.CBlockValAlt

open NumberField IsDedekindDomain Polynomial UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK UpperTheory.V.ZK.Cl

theorem UpperTheory.V.ZK.Cl.cJoin : CJoin := by
  intro hChain hFree hTriv hAct hSplit hSupp hLatLoc hMu hInt hVal hGtNe hGtEq hBetaDiv
    hBetaVal hRep hUnit
  intro sChain sPrism sPrismMul sZc sRel sEta sStein
  intro L F _ _ _ _ _ l c ν e _ ζ γ hL he α 𝔡 hD
  classical
  haveI : NeZero (l ^ ν) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hζq : ζ ^ (l ^ ν) = 1 := hL.prim.pow_eq_one
  have hR := hRep L F (l ^ ν) ζ hζq
  obtain ⟨kap, hkap⟩ := hR.2.2.2.2 hL.prim
  obtain ⟨b₀, hb₀, hsplit⟩ := hSplit L F hL.gal
  obtain ⟨b, hb, hb₀b, hbP⟩ := hSupp L F 𝔡 b₀ hb₀
  obtain ⟨n, t₀, hn, hrel⟩ := sRel l ν e
  obtain ⟨η, hη_ne, hη_eq⟩ := sEta l c ν (2 * e + 3) he hL.c_le t₀
  have hβ := hBetaDiv L F γ (1 + l ^ c) (2 * e + 3) (e + 1) (by omega) α 𝔡 hD
  set β := polAct γ (polE ((1 + l ^ c : ℕ) : ℤ) (2 * e + 3) (e + 1)) α with hβdef
  have hcar : ∀ t : Fin (2 * e + 4), ∃ g : GG L F (ZMod (l ^ ν) × ZMod (l ^ ν)),
      Carries L (l ^ ν) ζ (fun x => x.1 + ((t : ℕ) : ZMod (l ^ ν)) * x.2) (fun j => η j • 𝔡)
        (if t = t₀ then (fun x => if x = 1 then β else 1) else fun _ => 1) g := by
    intro t
    by_cases ht : t = t₀
    · subst ht
      rw [if_pos rfl]
      refine hGtEq sStein L F (ZMod (l ^ ν) × ZMod (l ^ ν)) l c ν (2 * e + 3) ζ γ hL _ η 𝔡
        (fun i => (pol ((1 + l ^ c : ℕ) : ℤ) (2 * e + 3)).coeff i) β ⟨(1, 0), by simp⟩ ?_ hβ
      rw [hη_eq]
      simp [pol]
    · rw [if_neg ht]
      exact hGtNe sStein L F (ZMod (l ^ ν) × ZMod (l ^ ν)) (l ^ ν) ζ _ η 𝔡 (hη_ne t ht)
  choose gG hgG using hcar
  have hmem : ∀ t, gG t ∈ GLoc F (ZMod (l ^ ν) × ZMod (l ^ ν)) b := by
    intro t
    refine hLatLoc L F (ZMod (l ^ ν) × ZMod (l ^ ν)) b hb 0 (fun j => η j • 𝔡) ?_ ?_ (gG t) (hgG t).1
    · intro j P h
      simp at h
    · intro j P h
      apply hbP P
      intro h0
      apply h
      simp [h0]
  set Gr := GLoc F (ZMod (l ^ ν) × ZMod (l ^ ν)) b with hGr
  set Hs := (StabP L (InLat (0 : ZMod (l ^ ν) × ZMod (l ^ ν) → HeightOneSpectrum (𝓞 F) →₀ ℤ))).subgroupOf Gr with hHs
  let gs : Fin (2 * e + 4) → Gr := fun t => ⟨gG t, hmem t⟩
  let ρD : Cq (l ^ ν) × Cq (l ^ ν) →* Gr := (repD L (l ^ ν) ζ hζq).codRestrict Gr (fun x => hR.2.2.1 b x)
  have memStab : ∀ (p : (ZMod (l ^ ν) × ZMod (l ^ ν) → F) → Prop) (g : GG L F (ZMod (l ^ ν) × ZMod (l ^ ν))),
      g ∈ StabP L p ↔ ∀ x, p x ↔ p (g x) := fun _ _ => Iff.rfl
  have hstab : ∀ (p p' : (ZMod (l ^ ν) × ZMod (l ^ ν) → F) → Prop) (g h : GG L F (ZMod (l ^ ν) × ZMod (l ^ ν))),
      (∀ x, p x ↔ p' (g x)) → (∀ x, p' x ↔ p' (h x)) → g⁻¹ * h * g ∈ StabP L p := by
    intro p p' g h hg hh
    rw [memStab]
    intro x
    rw [hg x, hg ((g⁻¹ * h * g) x)]
    simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]
    exact hh (g x)
  have hstab2 : ∀ (p p' : (ZMod (l ^ ν) × ZMod (l ^ ν) → F) → Prop) (g g' : GG L F (ZMod (l ^ ν) × ZMod (l ^ ν))),
      (∀ x, p x ↔ p' (g x)) → (∀ x, p x ↔ p' (g' x)) → g⁻¹ * g' ∈ StabP L p := by
    intro p p' g g' hg hg'
    rw [memStab]
    intro x
    rw [hg' x, hg ((g⁻¹ * g') x)]
    simp only [LinearEquiv.mul_apply, LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]
  have hcomm : ∀ (t : Fin (2 * e + 4)) (c' : Cq (l ^ ν)), Commute (gs t) (ρD (dt (l ^ ν) (t : ℕ) c')) := by
    intro t c'
    have hc := hR.2.2.2.1 _ _ _ _ _ (hgG t) c'
    apply Subtype.ext
    simp only [Subgroup.coe_mul, gs, ρD, MonoidHom.codRestrict_apply]
    rw [hR.1]
    exact hc.eq
  have hrhoH : ∀ x, ρD x ∈ Hs := by
    intro x
    rw [hHs, Subgroup.mem_subgroupOf]
    exact hR.2.1 0 x
  have hconj : ∀ x, (gs t₀)⁻¹ * ρD x * gs t₀ ∈ Hs := by
    intro x
    rw [hHs, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, gs, ρD, MonoidHom.codRestrict_apply]
    exact hstab _ _ _ _ (hgG t₀).1 ((memStab _ _).mp (hR.2.1 (fun j => η j • 𝔡) x))
  have hquot : ∀ t, (gs t)⁻¹ * gs t₀ ∈ Hs := by
    intro t
    rw [hHs, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, gs]
    exact hstab2 _ _ _ _ (hgG t).1 (hgG t₀).1
  obtain ⟨y, hyc, hyb⟩ := hChain (ZMod (l ^ ν)) (Cq (l ^ ν)) (Cq (l ^ ν) × Cq (l ^ ν)) Gr
    (Fin (2 * e + 4)) (2 * e + 1) Hs ρD (fun t => dt (l ^ ν) (t : ℕ)) n (zc (l ^ ν) e) gs t₀
    (sZc (l ^ ν) e) hrel hcomm hrhoH hconj hquot
  obtain ⟨hfin, hproj, αI, hαI⟩ := hInt L F (ZMod (l ^ ν) × ZMod (l ^ ν)) b
  haveI := hfin
  haveI := hproj
  obtain ⟨N, lam, hlam⟩ := hFree (𝓞 L) (ZMod (l ^ ν) × ZMod (l ^ ν) → 𝓞 F) Hs αI
  set w : ZMod (l ^ ν) := ((hn.unit⁻¹ : (ZMod (l ^ ν))ˣ) : ZMod (l ^ ν)) with hw
  set y' := w • y with hy'
  have hy'c : Cyc y' := by
    unfold Cyc at hyc ⊢
    rw [hy', map_smul, hyc, smul_zero]
  refine ⟨N, cm (ZMod (l ^ ν)) lam (2 * e + 1 + 1 + 1) y', algebraMap (𝓞 L) (𝓞 F) b, ?_, ?_, ?_⟩
  · unfold Cyc at hy'c ⊢
    rw [(sChain (ZMod (l ^ ν))).2.1]
    erw [hy'c, map_zero]
  · intro h
    apply hb
    exact FaithfulSMul.algebraMap_injective (𝓞 L) (𝓞 F) (by rw [h, map_zero])
  intro k _ _ r hr hrb hζ v θ hθ hv
  have hrb₀ : r (algebraMap (𝓞 L) (𝓞 F) b₀) ≠ 0 := by
    obtain ⟨c', hc'⟩ := hb₀b
    intro h0
    apply hrb
    rw [hc', map_mul, map_mul, h0, zero_mul]
  have hSp : Split L r := hsplit k r hr hrb₀
  obtain ⟨μ, hμ⟩ := hMu L F (ZMod (l ^ ν) × ZMod (l ^ ν)) k r b hrb hr hSp
  obtain ⟨U, f, hUdef, hUact, hfadd, hf1, hfres, hUres⟩ := hUnit L F k r b hrb (l ^ ν) v
  have hαU : α ∈ U := by
    rw [hUdef]
    intro P hP
    have h1 : 𝔡 P = 0 := by
      by_contra h0
      exact hP (hbP P h0)
    have h2 : 𝔡 (actP γ P) = 0 := by
      by_contra h0
      exact hP (((hAct L F).2.2.2.1 γ P b).mp (hbP _ h0))
    rw [hD P, h1, h2]
    simp
  have hnrmU : nrm γ ((1 + l ^ c) ^ (e + 1)) α ∈ U := by
    unfold nrm
    exact Subgroup.prod_mem U fun j _ => U.pow_mem (hUact _ _ hαU) _
  obtain ⟨u, hu⟩ := hUres _ hnrmU
  refine ⟨u, hu, ?_⟩
  rw [← hfres _ _ hu]
  obtain ⟨π, hπ1, hπ2, hπ3, hπ4⟩ := hαI k r hSp μ hμ
  obtain ⟨P, φ, hφ⟩ := hlam k (r.comp (algebraMap (𝓞 L) (𝓞 F))) hr
    (Gal(F/L) × (ZMod (l ^ ν) × ZMod (l ^ ν)) → k) π (μ.comp Hs.subtype) hπ1 hπ2 hπ3 hπ4
  beta_reduce at hyb
  rw [← (sChain (ZMod (l ^ ν))).2.2.1, hφ]
  refine Eq.trans (hTriv k (ZMod (l ^ ν)) (2 * e + 1 + 1) θ hθ Hs
    (Gal(F/L) × (ZMod (l ^ ν) × ZMod (l ^ ν)) → k) P (Fin N → k) (μ.comp Hs.subtype) φ y' hy'c) ?_
  rw [(sChain (ZMod (l ^ ν))).2.2.1]
  change θ (Gal(F/L) × (ZMod (l ^ ν) × ZMod (l ^ ν)) → k)
    (cm (ZMod (l ^ ν)) μ (2 * e + 1 + 2) (cm (ZMod (l ^ ν)) Hs.subtype (2 * e + 1 + 2) (w • y))) = _
  rw [map_smul, map_smul, map_smul]
  have hA : θ (Gal(F/L) × (ZMod (l ^ ν) × ZMod (l ^ ν)) → k)
      (cm (ZMod (l ^ ν)) μ (2 * e + 1 + 2) (cm (ZMod (l ^ ν)) Hs.subtype (2 * e + 1 + 2) y)) =
      ∑ t : Fin (2 * e + 4), n t • θ (Gal(F/L) × (ZMod (l ^ ν) × ZMod (l ^ ν)) → k)
        (cm (ZMod (l ^ ν)) μ (2 * e + 1 + 2) (prism (ZMod (l ^ ν)) (gs t) (2 * e + 1 + 1)
          (cm (ZMod (l ^ ν)) (ρD.comp (dt (l ^ ν) (t : ℕ))) (2 * e + 1 + 1) (zc (l ^ ν) e)))) := by
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hyb
    have h0 : θ (Gal(F/L) × (ZMod (l ^ ν) × ZMod (l ^ ν)) → k)
        (cm (ZMod (l ^ ν)) μ (2 * e + 1 + 2) (bd _ _ _ x)) = 0 :=
      hθ.bdry _ _ (LinearMap.mem_range.mpr ⟨cm (ZMod (l ^ ν)) μ _ x, (sChain _).2.1 _ _ μ _ x⟩)
    rw [hx, map_sub, map_sub, sub_eq_zero, map_sum, map_sum] at h0
    rw [h0]
    simp only [map_smul]
  have hT : ∀ t : Fin (2 * e + 4), θ (Gal(F/L) × (ZMod (l ^ ν) × ZMod (l ^ ν)) → k)
      (cm (ZMod (l ^ ν)) μ (2 * e + 1 + 2) (prism (ZMod (l ^ ν)) (gs t) (2 * e + 1 + 1)
        (cm (ZMod (l ^ ν)) (ρD.comp (dt (l ^ ν) (t : ℕ))) (2 * e + 1 + 1) (zc (l ^ ν) e)))) =
      ∑ σ, ∑ x, ((kap σ : ZMod (l ^ ν)) * x) ^ (e + 1) *
        f (actU σ ((if t = t₀ then (fun x => if x = 1 then β else 1) else fun _ => 1) x)) := by
    intro t
    erw [(sChain (ZMod (l ^ ν))).2.2.2.1, ← (sChain (ZMod (l ^ ν))).2.2.1]
    exact hVal L F (ZMod (l ^ ν) × ZMod (l ^ ν)) (l ^ ν) e ζ hζq kap hkap k r b hrb hSp μ hμ hζ v θ hθ hv
      f hfres _ _ _ (gs t) (ρD.comp (dt (l ^ ν) (t : ℕ))) (hgG t)
      (fun c' => by simp only [ρD, MonoidHom.comp_apply, MonoidHom.codRestrict_apply]; exact hR.1 t c')
  have hT0 : ∀ t : Fin (2 * e + 4), t ≠ t₀ →
      ∑ σ, ∑ x, ((kap σ : ZMod (l ^ ν)) * x) ^ (e + 1) *
        f (actU σ ((if t = t₀ then (fun x => if x = 1 then β else 1) else fun _ => 1) x)) = 0 := by
    intro t ht
    simp [if_neg ht, hf1]
  have hTt₀ : ∑ σ, ∑ x, ((kap σ : ZMod (l ^ ν)) * x) ^ (e + 1) *
        f (actU σ ((if t₀ = t₀ then (fun x => if x = 1 then β else 1) else fun _ => 1) x)) =
      ∑ σ, (kap σ : ZMod (l ^ ν)) ^ (e + 1) * f (actU σ β) := by
    rw [if_pos rfl]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.sum_eq_single (1 : ZMod (l ^ ν))]
    · simp
    · intro x _ hx
      simp [hx, hf1]
    · simp
  have hBV := hBetaVal L F l c ν (e + 1) ζ γ hL kap hkap U f hUact hfadd α hαU
    (polE ((1 + l ^ c : ℕ) : ℤ) (2 * e + 3) (e + 1))
  have hev : ((eval (((1 + l ^ c) ^ (e + 1) : ℕ) : ℤ) (polE ((1 + l ^ c : ℕ) : ℤ) (2 * e + 3) (e + 1)) : ℤ) :
      ZMod (l ^ ν)) = ((pe (1 + l ^ c) (2 * e + 3) (e + 1) : ℤ) : ZMod (l ^ ν)) := by
    congr 1
    simp [polE, pe, eval_prod]
  rw [hA, Finset.sum_eq_single t₀ (fun t _ ht => by rw [hT t, hT0 t ht, smul_zero]) (by simp),
    hT t₀, hTt₀, hBV, hev, smul_eq_mul, smul_eq_mul, ← mul_assoc, hw, hn.val_inv_mul, one_mul]
