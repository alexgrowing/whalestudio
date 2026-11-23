import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.CompDef

noncomputable section

namespace PositivityTheory.ThK

open scoped Matrix
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}

theorem one_mem_UAt (X : Spc F E n) (v : Pl F) : (1 : UA σ X.J) ∈ UAt σ X (evFin F v) := fun u _ => by
  have : mat (1 : UA σ X.J) = 1 := rfl
  rw [this, sub_self, smul_zero]

theorem mul_mem_UAt {X : Spc F E n} {v : Pl F} {g h : UA σ X.J} (hg : g ∈ UAt σ X (evFin F v)) (hh : h ∈ UAt σ X (evFin F v)) :
    g * h ∈ UAt σ X (evFin F v) := fun u hu => by
  have e : mat (g * h) - 1 = (mat g - 1) * mat h + (mat h - 1) := by
    have : mat (g * h) = mat g * mat h := rfl
    rw [this, sub_mul, one_mul]; abel
  rw [e, smul_add, ← Matrix.smul_mul, hg u hu, hh u hu, Matrix.zero_mul, add_zero]

theorem mat_inv_mul {X : Spc F E n} (g : UA σ X.J) : mat g⁻¹ * mat g = 1 := by
  have : mat (g⁻¹ * g) = mat g⁻¹ * mat g := rfl
  rw [← this, inv_mul_cancel]; rfl

theorem inv_mem_UAt {X : Spc F E n} {v : Pl F} {g : UA σ X.J} (hg : g ∈ UAt σ X (evFin F v)) :
    g⁻¹ ∈ UAt σ X (evFin F v) := fun u hu => by
  have e : mat g⁻¹ - 1 = -(mat g⁻¹ * (mat g - 1)) := by rw [mul_sub, mat_inv_mul, mul_one, neg_sub]
  rw [e, smul_neg, ← Matrix.mul_smul, hg u hu, Matrix.mul_zero, neg_zero]

variable (σ) in

def KSub (W : Spc F E d) (v : Pl F) : Subgroup (UA σ W.J) where
  carrier := KAt σ W v
  one_mem' := ⟨one_mem_UAt W v, fun y hy => by
    have : mat (1 : UA σ W.J) = 1 := rfl
    rw [inv_one, this, Matrix.one_mulVec]; exact ⟨hy, hy⟩⟩
  mul_mem' := fun {g h} hg hh => ⟨mul_mem_UAt hg.1 hh.1, fun y hy => by
    have e1 : mat (g * h) = mat g * mat h := rfl
    have e2 : mat (h⁻¹ * g⁻¹) = mat h⁻¹ * mat g⁻¹ := rfl
    rw [mul_inv_rev, e1, e2, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact ⟨(hg.2 _ (hh.2 y hy).1).1, (hh.2 _ (hg.2 y hy).2).2⟩⟩
  inv_mem' := fun {g} hg => ⟨inv_mem_UAt hg.1, fun y hy => by
    rw [inv_inv]; exact ⟨(hg.2 y hy).2, (hg.2 y hy).1⟩⟩

theorem exists_eigen_lift {K S T : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    [AddCommGroup S] [Module ℂ S] [AddCommGroup T] [Module ℂ T] (ω : K →* Module.End ℂ S) (c : K →* ℂˣ) (p : S →ₗ[ℂ] T) (f₀ : S)
    (hU : ∃ U ∈ 𝓝 (1 : K), ∀ k ∈ U, ω k f₀ = f₀ ∧ c k = 1) (hp : ∀ k, p (ω k f₀) = (c k : ℂ) • p f₀) :
    ∃ f, (∀ k, ω k f = (c k : ℂ) • f) ∧ p f = p f₀ := by
  classical
  let g : K → S := fun k => ((c k)⁻¹ : ℂˣ).1 • ω k f₀
  let H : Subgroup K :=
    { carrier := {k | ω k f₀ = (c k : ℂ) • f₀}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, Module.End.mul_apply, hb, map_smul, ha, smul_smul, map_mul, Units.val_mul, mul_comm]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        have h1 : ω a⁻¹ (ω a f₀) = f₀ := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
        rw [ha, map_smul] at h1
        rw [map_inv c, ← h1, smul_smul, h1, Units.inv_mul, one_smul] }
  obtain ⟨U, hU1, hU2⟩ := hU
  have hHo : IsOpen (H : Set K) := H.isOpen_of_mem_nhds (Filter.mem_of_superset hU1 fun k hk => by
    change ω k f₀ = (c k : ℂ) • f₀
    rw [(hU2 k hk).1, (hU2 k hk).2, Units.val_one, one_smul])
  haveI : Finite (K ⧸ H) := Subgroup.quotient_finite_of_isOpen H hHo
  letI : Fintype (K ⧸ H) := Fintype.ofFinite _
  have hg : ∀ a b : K, (a : K ⧸ H) = b → g a = g b := fun a b hab => by
    have hm : ω (a⁻¹ * b) f₀ = (c (a⁻¹ * b) : ℂ) • f₀ := QuotientGroup.eq.1 hab
    have : ω b f₀ = (c (a⁻¹ * b) : ℂ) • ω a f₀ := by
      rw [← map_smul, ← hm, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
    simp only [g]
    rw [this, smul_smul, map_mul, map_inv, Units.val_mul, mul_left_comm, Units.inv_mul, mul_one]
  have hN : (Fintype.card (K ⧸ H) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine ⟨(Fintype.card (K ⧸ H) : ℂ)⁻¹ • ∑ q : K ⧸ H, g q.out, fun k => ?_, ?_⟩
  · rw [map_smul, smul_comm (c k : ℂ), map_sum]
    congr 1
    rw [Finset.smul_sum, ← Equiv.sum_comp (MulAction.toPerm k) fun q : K ⧸ H => (c k : ℂ) • g q.out]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hg (MulAction.toPerm k q).out (k * q.out) (by
      rw [QuotientGroup.out_eq']; exact (MulAction.Quotient.mk_smul_out H k q).symm)]
    simp only [g]
    rw [map_smul, smul_smul, map_mul, mul_inv_rev, Units.val_mul, mul_left_comm, Units.mul_inv, mul_one, map_mul,
      Module.End.mul_apply]
  · rw [map_smul, map_sum]
    have : ∀ q : K ⧸ H, p (g q.out) = p f₀ := fun q => by
      simp only [g]
      rw [map_smul, hp, smul_smul, Units.inv_mul, one_smul]
    simp only [this, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hN, one_smul]

theorem augAt_le {X : Spc F E n} {W : Spc F E d} (om : Rep σ X W) (v : Pl F) : augAt om v ≤ SB _ :=
  Submodule.span_le.2 (by rintro _ ⟨g, -, φ, hφ, φ₁, h₁, -, rfl⟩; exact sub_mem h₁ hφ)

section Loc

variable {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ} {om : Rep σ X W} {v : Pl F}
  {ω : UA σ X.J × UA σ W.J → Module.End ℂ (Fn F n d v)} {ρ : Matrix (Fin n) (Fin d) (AE F E) → Module.End ℂ (Fn F n d v)}

theorem IsLocRep.mulW (L : IsLocRep M ψ om v ω ρ) {h h' : UA σ W.J} (hh : h ∈ UAt σ W (evFin F v)) (hh' : h' ∈ UAt σ W (evFin F v))
    {φ} (hφ : φ ∈ SB _) : ω (1, h * h') φ = ω (1, h) (ω (1, h') φ) := by
  simpa using L.mul 1 (one_mem_UAt X v) h hh 1 (one_mem_UAt X v) h' hh' φ hφ

theorem IsLocRep.ev_comp (L : IsLocRep M ψ om v ω ρ) {m : ℕ} {Cy : Matrix (Fin d) (Fin m) (AE F E)} (hC : At (evFin F v) Cy)
    {l : Fn F n d v →ₗ[ℂ] ℂ} (hl : IsEvAt M ψ v Cy l) {p : UA σ W.J} (hp : p ∈ PAt σ W v Cy) :
    IsEvAt M ψ v Cy (l ∘ₗ ω (1, p)) := by
  have hat : ∀ z : Matrix (Fin n) (Fin m) (AE F E), At (evFin F v) (z * Cyᵀ) := fun z u hu => by
    rw [← Matrix.mul_smul, ← Matrix.transpose_smul, hC u hu, Matrix.transpose_zero, Matrix.mul_zero]
  obtain ⟨hp, t, ht⟩ := hp
  intro z φ hφ φ₁ h
  rw [(L.actsH _ (hat z) φ hφ φ₁).1 h, LinearMap.comp_apply, LinearMap.comp_apply,
    L.impl 1 (one_mem_UAt X v) p hp _ (hat z) φ hφ]
  have e : mat (1 : UA σ X.J) * (z * Cyᵀ) * (mat p)ᵀ = (z * tᵀ) * Cyᵀ := by
    have : mat (1 : UA σ X.J) = 1 := rfl
    rw [this, Matrix.one_mul, Matrix.mul_assoc, ← Matrix.transpose_mul, ht, Matrix.transpose_mul, Matrix.mul_assoc]
  have hs := L.pres 1 (one_mem_UAt X v) p hp φ hφ
  rw [e]
  exact hl _ _ hs _ ((L.actsH _ (hat _) _ hs _).2 rfl)

theorem IsLocRep.exists_char (L : IsLocRep M ψ om v ω ρ) {φ} (hφ : φ ∈ SB _) (h0 : φ ≠ 0)
    (h : ∀ k ∈ KAt σ W v, ∃ c : ℂ, Acts (evFin F v) (om (1, k)) φ (c • φ)) :
    ∃ c : KSub σ W v →* ℂˣ, ∀ k : KSub σ W v, ω (1, k.1) φ = (c k : ℂ) • φ := by
  choose c hc using h
  have hc' : ∀ k : KSub σ W v, ω (1, k.1) φ = c k.1 k.2 • φ := fun k =>
    ((L.acts 1 (one_mem_UAt X v) k.1 k.2.1 φ hφ _).1 (hc k.1 k.2)).symm
  let c₀ : KSub σ W v →* ℂ :=
    { toFun := fun k => c k.1 k.2
      map_one' := smul_left_injective ℂ h0 (by
        change _ • φ = (1 : ℂ) • φ
        rw [← hc' 1, one_smul]; exact L.one φ hφ)
      map_mul' := fun a b => smul_left_injective ℂ h0 (by
        change _ • φ = (_ * _) • φ
        rw [← hc' (a * b), Subgroup.coe_mul, L.mulW a.2.1 b.2.1 hφ, hc' b, map_smul, hc' a, smul_smul, mul_comm]) }
  exact ⟨c₀.toHomUnits, hc'⟩

def IsLocRep.onK (L : IsLocRep M ψ om v ω ρ) : KSub σ W v →* Module.End ℂ (SB (Fin n × Fin d → Fv F v)) where
  toFun k := (ω (1, k.1)).restrict fun φ hφ => L.pres 1 (one_mem_UAt X v) k.1 k.2.1 φ hφ
  map_one' := LinearMap.ext fun φ => Subtype.ext (L.one φ φ.2)
  map_mul' a b := LinearMap.ext fun φ => Subtype.ext (L.mulW a.2.1 b.2.1 φ.2)

end Loc

section Main

variable {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} {v : Pl F}

theorem finAt_of {ω ρ ω' ρ'} (L : IsLocRep G.M B.ψ om v ω ρ) (L' : IsLocRep G.M' B.ψ om' v ω' ρ') (hv : v ∉ X.T)
    (hs : G.M.vac v ∈ SB _) (hs' : G.M'.vac v ∈ SB _)
    (hirr : ∀ N : Submodule ℂ (_ → ℂ), augAt om' v ≤ N → N ≤ SB _ → (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ N, ∀ φ₁ ∈ SB _,
      Acts (evFin F v) (om' (1, h)) φ φ₁ → φ₁ ∈ N) → N = augAt om' v ∨ N = SB _)
    (p : Fn F a (a + a') v →ₗ[ℂ] (Fn F a' (a + a') v ⧸ augAt om' v))
    (h1 : (SB _).map p = (SB _).map (augAt om' v).mkQ) (h2 : augAt om v ≤ LinearMap.ker p)
    (h3 : ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB _, ∀ φ' ∈ SB _, p φ = (augAt om' v).mkQ φ' →
      p (ω (1, h) φ) = (augAt om' v).mkQ (ω' (1, h) φ'))
    (h4 : p (G.M.vac v) = (augAt om' v).mkQ (G.M'.vac v)) (h5 : G.M'.vac v ∉ augAt om' v) :
    ∃ R, IsFinAt B G X om om' R v := by
  classical
  set q := (augAt om' v).mkQ with hq
  set Q := (SB (Fin a' × Fin (a + a') → Fv F v)).map q with hQ
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective Q.subtype Q.ker_subtype
  have hπ' : ∀ x (hx : x ∈ Q), π x = ⟨x, hx⟩ := fun x hx => LinearMap.congr_fun hπ ⟨x, hx⟩
  have mq : ∀ φ ∈ SB _, q φ ∈ Q := fun φ hφ => Submodule.mem_map_of_mem hφ
  have mp : ∀ φ ∈ SB _, p φ ∈ Q := fun φ hφ => h1 ▸ Submodule.mem_map_of_mem hφ
  have inj : ∀ x ∈ Q, ∀ y ∈ Q, π x = π y → x = y := fun x hx y hy h => by
    rw [hπ' x hx, hπ' y hy] at h; exact congrArg Subtype.val h
  let R : FinMaps F a a' :=
    { Pi := fun _ => Q
      p := fun u => if h : v = u then h ▸ (π ∘ₗ p) else 0
      p' := fun u => if h : v = u then h ▸ (π ∘ₗ q) else 0 }
  have e : R.p v = π ∘ₗ p := dif_pos rfl
  have e' : R.p' v = π ∘ₗ q := dif_pos rfl
  have on' : ∀ x : Q, ∃ φ ∈ SB _, q φ = x := fun x => x.2
  have on : ∀ x : Q, ∃ φ ∈ SB _, p φ = x := fun x => (h1.symm ▸ x.2 : x.1 ∈ (SB _).map p)
  have hx : ∀ x : Q, π x.1 = x := fun x => hπ' x.1 x.2
  have hne : π (q (G.M'.vac v)) ≠ 0 := fun h => h5 ((Submodule.Quotient.mk_eq_zero _).1
    (inj _ (mq _ hs') 0 Q.zero_mem (h.trans (map_zero π).symm)))
  have o1 := one_mem_UAt (σ := σ) G.V v
  have o1' := one_mem_UAt (σ := σ) G.V' v
  refine ⟨R, ?_, ?_, ?_, ?_, ?_, ⟨_, _, hne⟩, ?_, fun _ => ?_, fun _ h => absurd h hv⟩
  · rw [e, eq_top_iff]
    intro x _
    obtain ⟨φ, hφ, h⟩ := on x
    exact ⟨φ, hφ, by rw [LinearMap.comp_apply, h, hx]⟩
  · rw [e', eq_top_iff]
    intro x _
    obtain ⟨φ, hφ, h⟩ := on' x
    exact ⟨φ, hφ, by rw [LinearMap.comp_apply, h, hx]⟩
  · rw [e]
    exact h2.trans (LinearMap.ker_le_ker_comp _ _)
  · rw [e']
    exact (Submodule.ker_mkQ _).ge.trans (LinearMap.ker_le_ker_comp _ _)
  · intro h hh φ hφ φ' hφ' φ₁ _ φ₁' _ a1 a2 heq
    rw [e, e'] at heq ⊢
    rw [(L.acts 1 o1 h hh φ hφ _).1 a1, (L'.acts 1 o1' h hh φ' hφ' _).1 a2]
    exact congrArg π (h3 h hh φ hφ φ' hφ' (inj _ (mp _ hφ) _ (mq _ hφ') heq))
  · intro N hN
    rw [e] at hN
    have := hirr (SB _ ⊓ N.comap (π ∘ₗ q)) (le_inf (augAt_le om' v) fun φ hφ => by
        change π (q φ) ∈ N
        rw [show q φ = 0 from (Submodule.Quotient.mk_eq_zero _).2 hφ, map_zero]; exact N.zero_mem) inf_le_left
      fun h hh φ' hφ' φ₁' h₁ a2 => ⟨h₁, by
        obtain ⟨φ, hφ, hpq⟩ := on ⟨q φ', mq _ hφ'.1⟩
        have := hN h hh φ hφ _ (L.pres 1 o1 h hh φ hφ) ((L.acts 1 o1 h hh φ hφ _).2 rfl) (by
          change π (p φ) ∈ N
          rw [hpq]; exact hφ'.2)
        change π (q φ₁') ∈ N
        rw [(L'.acts 1 o1' h hh φ' hφ'.1 _).1 a2, ← h3 h hh φ hφ φ' hφ'.1 hpq]
        exact this⟩
    refine this.imp (fun h => ?_) fun h => ?_
    · rw [eq_bot_iff]
      intro x hxN
      obtain ⟨φ, hφ, hh⟩ := on' x
      have : φ ∈ augAt om' v := h ▸ (⟨hφ, by change π (q φ) ∈ N; rw [hh, hx]; exact hxN⟩ : φ ∈ SB _ ⊓ N.comap (π ∘ₗ q))
      exact Subtype.ext (hh.symm.trans ((Submodule.Quotient.mk_eq_zero _).2 this))
    · rw [eq_top_iff]
      intro x _
      obtain ⟨φ, hφ, hh⟩ := on' x
      have : φ ∈ SB _ ⊓ N.comap (π ∘ₗ q) := h.symm ▸ hφ
      have h6 : π (q φ) ∈ N := this.2
      rwa [hh, hx] at h6
  · rw [e, e']
    exact ⟨congrArg π h4, fun h => hne ((congrArg π h4).symm.trans h)⟩

end Main

theorem finInert_of (hKS : CompAtTriple) (hR : CoinvEmbeds) (hA : LocRepEx) (hB1 : KCompact)
    (hB2 : Iwasawa) (hC1 : EvLine) (hC2 : EvVac) (hD : VacEigen) (hE : InertOf) : FinInert := by
  classical
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v ⟨hv, he⟩
  obtain ⟨w, hw⟩ := hE F E σ B hT.base v he
  have P : PairOK B G.V G.W G.M om := ⟨hT.base, ⟨_, _, hT.geo.hV⟩, ⟨_, _, hT.geo.hW⟩, hT.geo.hM, _, _, hT.weil⟩
  have P' : PairOK B G.V' G.W G.M' om' := ⟨hT.base, ⟨_, _, hT.geo.hV'⟩, ⟨_, _, hT.geo.hW⟩, hT.geo.hM', _, _, hT.weil'⟩
  obtain ⟨ω, ρ, L⟩ := hA F E σ _ _ B _ _ _ _ P v
  obtain ⟨ω', ρ', L'⟩ := hA F E σ _ _ B _ _ _ _ P' v
  obtain ⟨-, hirr, p, h1, h2, h3⟩ := hKS F E σ B a a' G X om om' hT v w hw hv
  obtain ⟨m, Cy, hL, hAd, hIw, hch⟩ := hB2 F E σ _ _ B _ _ _ _ P v hT.geo.even ⟨w, hw⟩
  obtain ⟨l, hl, hl0⟩ := hC2 F E σ _ _ B _ _ _ _ P v ⟨w, hw⟩ m Cy hL hAd
  obtain ⟨l', hl', hl0'⟩ := hC2 F E σ _ _ B _ _ _ _ P' v ⟨w, hw⟩ m Cy hL hAd
  obtain ⟨hs, hn, -⟩ := hT.geo.hM.vac v
  obtain ⟨hs', hn', -⟩ := hT.geo.hM'.vac v
  obtain ⟨R1, R2⟩ := hR F E σ B a a' G X om om' hT v w hw hv m Cy hL
  have o1 := one_mem_UAt (σ := σ) G.V v
  have o1' := one_mem_UAt (σ := σ) G.V' v
  have oW := one_mem_UAt (σ := σ) G.W v
  have h5 : G.M'.vac v ∉ augAt om' v := fun h => hl0' ((R2 l' hl' ⟨_, hs', hl0'⟩ _ hs').1 h 1 oW _
    ((L'.acts 1 o1' 1 oW _ hs' _).2 (L'.one _ hs').symm))
  have h3' : ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB _, ∀ φ' ∈ SB _, p φ = (augAt om' v).mkQ φ' →
      p (ω (1, h) φ) = (augAt om' v).mkQ (ω' (1, h) φ') := fun h hh φ hφ φ' hφ' =>
    h3 h hh φ hφ φ' hφ' _ (L.pres 1 o1 h hh φ hφ) _ (L'.pres 1 o1' h hh φ' hφ') ((L.acts 1 o1 h hh φ hφ _).2 rfl)
      ((L'.acts 1 o1' h hh φ' hφ' _).2 rfl)
  obtain ⟨c, hc⟩ := L.exists_char hs hn (hD F E σ _ _ B _ _ _ _ P v)
  obtain ⟨c', hc'⟩ := L'.exists_char hs' hn' (hD F E σ _ _ B _ _ _ _ P' v)
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) (AE F E)
  haveI : IsTopologicalGroup (GL (Fin (a + a')) (AE F E)) := inferInstance
  haveI : IsTopologicalGroup (UA σ G.W.J) := inferInstance
  haveI : IsTopologicalGroup (KSub σ G.W v) := inferInstance
  haveI : CompactSpace (KSub σ G.W v) := isCompact_iff_compactSpace.1 (hB1 F E σ _ _ B _ _ _ _ P v)
  obtain ⟨f₀, hf₀, hpf₀⟩ : (augAt om' v).mkQ (G.M'.vac v) ∈ (SB _).map p := h1 ▸ Submodule.mem_map_of_mem hs'
  obtain ⟨f, hf, hpf⟩ := exists_eigen_lift L.onK c' (p ∘ₗ (SB _).subtype) ⟨f₀, hf₀⟩ (by
      obtain ⟨U, hU, hU'⟩ := L.smooth f₀ hf₀
      obtain ⟨U₁, hU₁, hU₁'⟩ := L'.smooth _ hs'
      refine ⟨Subtype.val ⁻¹' (U ∩ U₁), continuous_subtype_val.continuousAt (Filter.inter_mem hU hU₁), fun k hk =>
        ⟨Subtype.ext (hU' k.1 hk.1 k.2.1), Units.ext (smul_left_injective ℂ hn' ?_)⟩⟩
      change _ • _ = (1 : ℂ) • _
      rw [← hc' k, one_smul]
      exact hU₁' k.1 hk.2 k.2.1)
    fun k => by
      change p (ω (1, k.1) f₀) = _ • p f₀
      rw [h3' k.1 k.2.1 f₀ hf₀ _ hs' hpf₀, hc' k, map_smul, hpf₀]
  have hf' : ∀ k : KSub σ G.W v, ω (1, k.1) f.1 = (c' k : ℂ) • f.1 := fun k => congrArg Subtype.val (hf k)
  have hpf' : p f.1 = (augAt om' v).mkQ (G.M'.vac v) := hpf.trans hpf₀
  have hγ : ∀ g ∈ PAt σ G.W v Cy, ∃ γ : ℂ, ∀ φ ∈ SB _, l (ω (1, g) φ) = γ * l φ := fun g hg =>
    hC1 F E σ _ _ B _ _ _ _ P v m Cy hL l _ hl (L.ev_comp hL.supp hl hg) ⟨_, hs, hl0⟩
  have key : ∀ z ∈ SB _, (∀ k : KSub σ G.W v, ∃ t : ℂ, ω (1, k.1) z = t • z) → l z = 0 → z ∈ augAt om v := fun z hz hk h0 =>
    (R1 l hl ⟨_, hs, hl0⟩ z hz).2 fun h hh φ₁ ha => by
      obtain ⟨g, hg, k, hkK, rfl⟩ := hIw h hh
      obtain ⟨γ, hγ'⟩ := hγ g hg
      obtain ⟨t, ht⟩ := hk ⟨k, hkK⟩
      rw [(L.acts 1 o1 _ hh z hz _).1 ha, L.mulW hg.1 hkK.1 hz, hγ' _ (L.pres 1 o1 k hkK.1 z hz), ht, map_smul, h0,
        smul_zero, mul_zero]
  have hlf : l f.1 ≠ 0 := fun h0 => h5 ((Submodule.Quotient.mk_eq_zero _).1
    (hpf'.symm.trans (h2 (key f.1 f.2 (fun k => ⟨_, hf' k⟩) h0))))
  have hcc : ∀ k : KSub σ G.W v, c k = c' k := fun k => by
    have := hch (fun g => if hg : g ∈ KSub σ G.W v then ((c ⟨g, hg⟩ / c' ⟨g, hg⟩ : ℂˣ) : ℂ) else 0)
      (fun g hg g' hg' => by
        have hg₁ : g ∈ KSub σ G.W v := hg
        have hg₂ : g' ∈ KSub σ G.W v := hg'
        rw [dif_pos (mul_mem hg₁ hg₂), dif_pos hg₁, dif_pos hg₂, ← Units.val_mul, div_mul_div_comm, ← map_mul, ← map_mul]
        rfl)
      (fun g hg hgP => by
        have hg₁ : g ∈ KSub σ G.W v := hg
        obtain ⟨γ, hγ'⟩ := hγ g hgP
        have a1 := hγ' _ hs
        have a2 := hγ' _ f.2
        rw [hc ⟨g, hg₁⟩, map_smul, smul_eq_mul] at a1
        rw [hf' ⟨g, hg₁⟩, map_smul, smul_eq_mul] at a2
        have : c ⟨g, hg₁⟩ = c' ⟨g, hg₁⟩ :=
          Units.ext ((mul_right_cancel₀ hl0 a1).trans (mul_right_cancel₀ hlf a2).symm)
        rw [dif_pos hg₁, this, div_self', Units.val_one]) k.1 k.2
    rw [dif_pos k.2] at this
    exact div_eq_one.1 (Units.ext this)
  set t := l f.1 / l (G.M.vac v) with ht
  have ht0 : t ≠ 0 := div_ne_zero hlf hl0
  have hz := h2 (key (f.1 - t • G.M.vac v) (sub_mem f.2 (Submodule.smul_mem _ _ hs))
    (fun k => ⟨c k, by rw [map_sub, map_smul, hf' k, hc k, ← hcc k, smul_sub, smul_comm]⟩)
    (by rw [map_sub, map_smul, smul_eq_mul, ht, div_mul_cancel₀ _ hl0, sub_self]))
  rw [LinearMap.mem_ker, map_sub, map_smul, hpf', sub_eq_zero] at hz
  refine finAt_of L L' hv hs hs' hirr (t • p) ((Submodule.map_smul _ _ _ ht0).trans h1)
    (fun φ hφ => by rw [LinearMap.mem_ker, LinearMap.smul_apply, h2 hφ, smul_zero]) (fun h hh φ hφ φ' hφ' e => ?_) hz.symm h5
  rw [LinearMap.smul_apply, ← map_smul] at e ⊢
  rw [← map_smul]
  exact h3' h hh _ (Submodule.smul_mem _ _ hφ) _ hφ' e

end PositivityTheory.ThK
