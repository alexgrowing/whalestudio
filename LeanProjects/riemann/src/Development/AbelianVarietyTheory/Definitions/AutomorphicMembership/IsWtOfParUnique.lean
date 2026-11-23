import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BrgStdR
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EventuallyCongOne
import Formalism.LocalToGlobal.Columns.BaseLemmas
import Formalism.LocalToGlobal.Columns.RowFormsLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcParameterEAddHalfShiftLeBSucc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoefDualPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Col Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
open GlobalTheory.Mem GlobalTheory.Mem.Col2
open scoped TensorProduct

namespace GlobalTheory.Mem.R3.StdModel

theorem matEq_refl {A : Type} [CommRing A] {a : ℕ} (x : GL (Fin a) A) : MatEq x x :=
  ⟨rfl, fun i j i' j' a b => by obtain rfl := Fin.ext a; obtain rfl := Fin.ext b; rfl⟩

theorem eq_of_matEq {A : Type} [CommRing A] {a : ℕ} {x y : GL (Fin a) A} (h : MatEq x y) : x = y :=
  Units.ext (Matrix.ext fun i j => h.2 i j i j rfl rfl)

section Gen

variable {X : Fields} {n : ℕ} (σ : X.K →+* ℂ)

def crd (lam : X.Tau → DomWeight n) : VV X.K lam →ₛₗ[σ] (VVIdx lam → ℂ) where
  toFun v i := σ ((bVV X.K lam).repr v i)
  map_add' v w := by funext i; simp
  map_smul' a v := by funext i; simp

theorem crd_li (lam : X.Tau → DomWeight n) : LinearIndependent ℂ fun i => crd σ lam (bVV X.K lam i) := by
  classical
  have : (fun i => crd σ lam (bVV X.K lam i)) = fun i => Pi.basisFun ℂ (VVIdx lam) i := by
    funext i j
    show σ ((bVV X.K lam).repr (bVV X.K lam i) j) = _
    rw [Module.Basis.repr_self, Pi.basisFun_apply, Finsupp.single_apply, Pi.single_apply]
    by_cases h : i = j
    · simp [h]
    · simp [h, Ne.symm h]
  rw [this]
  exact (Pi.basisFun ℂ (VVIdx lam)).linearIndependent

def actC (lam : X.Tau → DomWeight n) (f : Module.End X.K (VV X.K lam)) (w : VVIdx lam → ℂ) : VVIdx lam → ℂ :=
  ∑ j, w j • crd σ lam (f (bVV X.K lam j))

theorem expand {W : Type} [AddCommGroup W] [Module ℂ W] {lam : X.Tau → DomWeight n} (c : VV X.K lam →ₛₗ[σ] W) (v : VV X.K lam) :
    c v = ∑ j, σ ((bVV X.K lam).repr v j) • c (bVV X.K lam j) := by
  conv_lhs => rw [← (bVV X.K lam).sum_repr v]
  rw [map_sum]
  simp only [map_smulₛₗ]

theorem crd_act (lam : X.Tau → DomWeight n) (f : Module.End X.K (VV X.K lam)) (v : VV X.K lam) :
    crd σ lam (f v) = actC σ lam f (crd σ lam v) := by
  have := expand σ ((crd σ lam).comp f) v
  exact this

theorem inj_of_li {W : Type} [AddCommGroup W] [Module ℂ W] {lam : X.Tau → DomWeight n} (c : VV X.K lam →ₛₗ[σ] W)
    (h : LinearIndependent ℂ fun i => c (bVV X.K lam i)) (v : VV X.K lam) (hv : c v = 0) : v = 0 := by
  rw [expand σ c v] at hv
  have := Fintype.linearIndependent_iff.1 h _ hv
  apply (bVV X.K lam).repr.injective
  ext j
  simpa using this j

variable [NeZero n]

theorem stdSide_model (hc : CMData X.F X.E) {ι : Type} (lam : X.Tau → DomWeight n)
    (rho : GL (Fin n) X.E →* Module.End X.K (VV X.K lam)) (SG : ι → Finset (Pl X.E)) (Fm : ι → Type)
    (val : ∀ t, Fm t → DecoSet X.E n ∅ (SG t) → VV X.K lam) :
    StdSide (a := n) (H := Formalism.L2.Col.UAd hc n) (Γ := GL (Fin n) X.E) σ (fun h => h.1) (fun γ g => γ = g)
      (fun γ => actC σ lam (rho γ)) lam rho SG Fm val
      fun t φ h => crd σ lam (val t φ (decoPt hc n ∅ (SG t) (QuotientGroup.mk h))) := by
  refine ⟨crd σ lam, ?_, ?_, crd_li σ lam, hc, fun h => ⟨h, matEq_refl _⟩⟩
  · rintro γ _ g rfl hm v
    rw [← eq_of_matEq hm]
    exact crd_act σ lam _ v
  · intro hc' t φ h x hm
    obtain rfl : h = x := Subtype.ext (eq_of_matEq hm)
    rfl

variable {σ} {a : ℕ} {H Γ W : Type} [AddCommGroup W] [Module ℂ W]
  {mat : H → GL (Fin a) (X.E ⊗[X.F] Formalism.L2.Herm.Af X.F)} {rat : Γ → GL (Fin a) X.E → Prop} {ρ : Γ → W → W}
  {ι : Type} {lam : X.Tau → DomWeight n} {rho : GL (Fin n) X.E →* Module.End X.K (VV X.K lam)}

theorem ad_ne_zero {SG : ι → Finset (Pl X.E)} {Fm : ι → Type} {val : ∀ t, Fm t → DecoSet X.E n ∅ (SG t) → VV X.K lam}
    {ad : ∀ t, Fm t → H → W} (s : StdSide σ mat rat ρ lam rho SG Fm val ad) (t : ι) (φ : Fm t) (hφ : ∀ d, val t φ d ≠ 0) (h : H) :
    ad t φ h ≠ 0 := by
  obtain ⟨c, hli, hv⟩ := s.value
  obtain ⟨d, hd⟩ := hv h t
  rw [hd]
  exact fun e => hφ d (inj_of_li σ c hli _ e)

theorem ad_eq {S : Finset (Pl X.E)} {Fm : ι → Type} {val : ∀ t, Fm t → DecoSet X.E n ∅ S → VV X.K lam}
    {ad : ∀ t, Fm t → H → W} (s : StdSide σ mat rat ρ lam rho (fun _ => S) Fm val ad) (t t' : ι) (φ : Fm t) (φ' : Fm t')
    (e : val t φ = val t' φ') : ad t φ = ad t' φ' := by
  obtain ⟨c, -, hr, -, hc, hx⟩ := s
  funext h
  obtain ⟨x, hm⟩ := hx h
  rw [hr hc t φ h x hm, hr hc t' φ' h x hm, e]

theorem one_map {SG : ι → Finset (Pl X.E)} {Fm : ι → Type} {val : ∀ t, Fm t → DecoSet X.E n ∅ (SG t) → VV X.K lam}
    {ad ad' : ∀ t, Fm t → H → W} (s : StdSide σ mat rat ρ lam rho SG Fm val ad) (s' : StdSide σ mat rat ρ lam rho SG Fm val ad') :
    ∃ T : W →ₗ[ℂ] W, ∀ t φ h, ad' t φ h = T (ad t φ h) := by
  obtain ⟨c, -, hr, hli, hc, hx⟩ := s
  obtain ⟨c', -, hr', -, -⟩ := s'
  obtain ⟨T, hT⟩ := LinearMap.exists_extend ((Module.Basis.span hli).constr ℂ fun i => c' (bVV X.K lam i))
  have hb : ∀ i, T (c (bVV X.K lam i)) = c' (bVV X.K lam i) := fun i => by
    have := LinearMap.congr_fun hT (Module.Basis.span hli i)
    rw [Module.Basis.constr_basis, LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.span_apply] at this
    exact this
  refine ⟨T, fun t φ h => ?_⟩
  obtain ⟨x, hm⟩ := hx h
  rw [hr hc t φ h x hm, hr' hc t φ h x hm, expand σ c, expand σ c', map_sum]
  simp only [map_smul, hb]

theorem not_sign [Nonempty H] {S : Finset (Pl X.E)} (v : VV X.K lam) (hv : v ≠ 0) (f : H → W) :
    ¬ StdSide σ mat rat ρ lam rho (fun _ : Bool => S) (fun _ => Unit) (fun _ _ _ => v) fun b _ => cond b f (-f) := by
  intro s
  have e := ad_eq s true false () () rfl
  obtain ⟨h⟩ := ‹Nonempty H›
  have h0 := ad_ne_zero s true () (fun _ => hv) h
  have e1 : f h = -f h := congrFun e h
  have h2 : (2 : ℂ) • f h = 0 := by rw [two_smul]; exact add_eq_zero_iff_eq_neg.2 e1
  exact h0 ((smul_eq_zero.1 h2).resolve_left two_ne_zero)

theorem transport {K E ι' : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Fintype ι'] (σ : K →+* ℂ) {a n : ℕ} (e : a = n)
    (lam : ι' → DomWeight a) (lam' : ι' → DomWeight n)
    (hl : ∀ τ (i : Fin a) (i' : Fin n), (i : ℕ) = i' → (lam τ).w i = (lam' τ).w i')
    (r : ∀ {k : ℕ} (l : ι' → DomWeight k), GL (Fin k) E →* Module.End K (VV K l))
    (c0 : VV K lam →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun i => c0 (bVV K lam i)) {Γ : Type} (rat : Γ → GL (Fin a) E → Prop)
    (ρ : Γ → W → W) (hi : ∀ γ γE, rat γ γE → ∀ v, c0 (r lam γE v) = ρ γ (c0 v)) :
    ∃ c : VV K lam' →ₛₗ[σ] W, (∀ γ γE g, rat γ γE → MatEq γE g → ∀ v, c (r lam' g v) = ρ γ (c v)) ∧
      LinearIndependent ℂ fun i => c (bVV K lam' i) := by
  subst e
  obtain rfl : lam = lam' := by
    funext τ
    have : (lam τ).w = (lam' τ).w := funext fun i => hl τ i i rfl
    cases h1 : lam τ
    cases h2 : lam' τ
    rw [h1, h2] at this
    simp only at this
    subst this
    rfl
  refine ⟨c0, fun γ γE g h hm v => ?_, hli⟩
  rw [← eq_of_matEq hm]
  exact hi γ γE h v

end Gen

section Rec

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isWtOfPar_unique {N N' : ℕ} {S : SPar} (hS : ∀ x ∈ S, x.2 = true) {lam : DomWeight N} {lam' : DomWeight N'}
    (h : Bridge.IsWtOfPar lam S) (h' : Bridge.IsWtOfPar lam' S) (i : Fin N) (i' : Fin N') (e : (i : ℕ) = i') :
    lam.w i = lam'.w i' := by
  obtain ⟨hc, c, ha, hm, hw⟩ := h
  obtain ⟨hc', c', ha', hm', hw'⟩ := h'
  obtain rfl : N = N' := hc.symm.trans hc'
  obtain rfl : i = i' := Fin.ext e
  have key : ∀ (d : Fin N → ℚ), StrictAnti d → (∀ i, ∃ s, (d i, s) ∈ S) → Set.range d = {y | (y, true) ∈ S} := by
    intro d hd hmem
    have h1 : (Finset.univ.image fun i => (d i, true)) = S := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
        obtain ⟨s, hs⟩ := hmem i
        have := hS _ hs
        simp only at this
        exact this ▸ hs
      · rw [Finset.card_image_of_injective _ (fun a b q => hd.injective (Prod.ext_iff.1 q).1), hc]
        simp
    ext y
    simp [← h1]
  have : c = c' := (ha.range_inj ha').1 ((key c ha hm).trans (key c' ha' hm').symm)
  have q := (hw i).trans (this ▸ (hw' i).symm)
  exact_mod_cast q

theorem isWtOfPar_sgTrue (D : D7) (τ : D.what₂.Tau) :
    Bridge.IsWtOfPar (RowPar.of (D.hc τ)).sgTrue ((Ptw D).Dpar D.R.m τ) := by
  have hk := D.R.m_add_three_le_k
  have hr : D.sp.X'.rank = D.R.N D.R.m - 1 := by rw [D.sp.X'_rank, rank_X'_eq]; rfl
  refine ⟨hr ▸ (GlobalTheory.ForcedWeights.lamRForced D τ).1, fun i => (RowPar.of (D.hc τ)).sgHC i.1 - RowPar.sh D.R, ?_, ?_,
    fun i => RowPar.sgTrue_eq _ i⟩
  · intro i j hij
    have h1 := RowPar.sgTrue_eq (D.hc τ) i
    have h2 := RowPar.sgTrue_eq (D.hc τ) j
    have h3 : (((RowPar.of (D.hc τ)).sgTrue.w j : ℤ) : ℚ) ≤ (RowPar.of (D.hc τ)).sgTrue.w i := by
      exact_mod_cast (RowPar.of (D.hc τ)).sgTrue.anti hij.le
    have h4 : ((i : ℕ) : ℚ) < (j : ℕ) := by exact_mod_cast hij
    simp only [rhoVec] at h1 h2
    simp only
    linarith
  · intro i
    refine ⟨true, ?_⟩
    rw [GlobalTheory.ForcedWeights.dpar_eq, Finset.mem_image]
    have hi := i.2
    unfold Ranks.N at hi
    by_cases h1 : i.1 < D.R.k - 1
    · exact ⟨.inl ⟨i.1, h1⟩, Finset.mem_univ _, by simp [GlobalTheory.ForcedWeights.entry, RowPar.sgHC, RowPar.sh, h1, RowPar.of]⟩
    · have hq : (i.1 - (D.R.k - 1)) / (D.R.t + 1) < D.R.m := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]; omega
      by_cases h2 : (i.1 - (D.R.k - 1)) % (D.R.t + 1) = 0
      · exact ⟨.inr (.inl ⟨_, hq⟩), Finset.mem_univ _, by
          simp [GlobalTheory.ForcedWeights.entry, RowPar.sgHC, RowPar.sh, h1, h2, RowPar.of, RowPar.bAt, hq]⟩
      · have h3 : (i.1 - (D.R.k - 1)) % (D.R.t + 1) < D.R.t + 1 := Nat.mod_lt _ (by omega)
        refine ⟨.inr (.inr (⟨_, hq⟩, ⟨(i.1 - (D.R.k - 1)) % (D.R.t + 1) - 1, by omega⟩)), Finset.mem_univ _, ?_⟩
        simp only [GlobalTheory.ForcedWeights.entry, RowPar.sgHC, RowPar.sh, h1, h2, RowPar.of, RowPar.eAt, hq, dite_true, dite_false,
          if_false, Prod.mk.injEq, and_true]
        rw [Nat.cast_sub (by omega)]
        push_cast
        ring

theorem lamRdef_eq (X : Stages) (τ) (i : Fin X.toD7.sp.X'.rank) (i' : Fin (X.B.R.N X.B.R.m - 1)) (e : (i : ℕ) = i') :
    (Bridge.lamRdef (Ptw X.toD7) τ).w i = (X.B.wts.sgTrue τ).w i' := by
  refine isWtOfPar_unique ?_ (GlobalTheory.ForcedWeights.lamRForced X.toD7 τ) (isWtOfPar_sgTrue X.toD7 τ) i i' e
  rw [GlobalTheory.ForcedWeights.dpar_eq]
  intro x hx
  obtain ⟨_, -, rfl⟩ := Finset.mem_image.1 hx
  rfl

theorem labLL_eq (X : Stages) : labLL X.toD7 = X.B.fields.emb := rfl

theorem exists_matEq {D : D7} (V : HSp D) {n : ℕ} (hn : V.rank = n) (hG : V.gram = 1) (h : Bridge.Gf V) :
    ∃ x : UAd D.sp.cm n, R3.MatEq (R3.matIn V 1 h) (x : GL (Fin n) _) := by
  obtain ⟨_, g, rfl⟩ := h
  refine ⟨⟨_, GlobalTheory.Mem.ColAd.finN_mem hn hG g⟩, ?_⟩
  subst hn
  refine ⟨rfl, fun i j i' j' a b => ?_⟩
  obtain rfl := Fin.ext a
  obtain rfl := Fin.ext b
  unfold R3.matIn
  rw [mul_one]
  rfl

theorem lamLdef_eq (X : Stages) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ X.B.R.m) (τ) (i : Fin (X.toD7.sp.V j).rank) (i' : Fin X.B.R.nV)
    (e : (i : ℕ) = i') : (Bridge.lamLdef (D := X.toD7) (X.toD7.sp.V j).rank j τ).w i = (X.B.wts.lamV j τ).w i' := by
  obtain ⟨hj, W, hk, hm, ht, hjj, he, hv, hb, hw⟩ := GlobalTheory.ForcedWeights.lamLForced X.toD7 j h1 h2 τ
  have hk : W.k = X.B.R.k := hk
  have hm : W.m = X.B.R.m := hm
  have ht : W.t = X.B.R.t := ht
  have he : (W.e : ℚ) = (X.B.hc τ).e ⟨j - 1, hj.2⟩ := he
  have hv : ∀ a : Fin (X.B.R.k - 1), (W.v (a + 2) : ℚ) = (X.B.hc τ).v a := hv
  have hb : ∀ a : Fin X.B.R.m, (W.b (a + 1) : ℚ) = (X.B.hc τ).b a := hb
  have hkm := X.B.R.m_add_three_le_k
  have q := RowPar.lamV_eq (X.B.hc τ) h1 h2 i'
  have hi := i'.2
  have hE : (RowPar.of (X.B.hc τ)).eAt (j - 1) = W.e := by
    rw [he]; exact dif_pos hj.2
  have hB : ∀ n, n < X.B.R.m → (RowPar.of (X.B.hc τ)).bAt n = W.b (n + 1) := fun n hn => by
    rw [hb ⟨n, hn⟩]; exact dif_pos hn
  have key : W.lamPrime (i'.1 + 1) = (RowPar.of (X.B.hc τ)).lamVQ j i' := by
    unfold Ranks.nV Ranks.r at hi
    unfold IndefiniteWeightData.WeightData.lamPrime IndefiniteWeightData.WeightData.thetaWt IndefiniteWeightData.WeightData.dTau IndefiniteWeightData.WeightData.aPlus IndefiniteWeightData.WeightData.aMinus
      IndefiniteWeightData.WeightData.lam IndefiniteWeightData.WeightData.nV IndefiniteWeightData.WeightData.r IndefiniteWeightData.WeightData.p IndefiniteWeightData.WeightData.q
      RowPar.lamVQ RowPar.aPlus RowPar.aMinusRev RowPar.dV RowPar.vb RowPar.pOf RowPar.qOf
    rw [hk, hm, ht, hjj, hE]
    congr 1
    by_cases a : i'.1 < X.B.R.k + j - 1
    · rw [if_pos a, if_pos (show i'.1 + 1 ≤ _ from a), Nat.add_sub_cancel]
      by_cases b : i'.1 < X.B.R.k - 1
      · rw [dif_pos b, if_pos (show i'.1 + 1 ≤ _ from b), hv ⟨_, b⟩]
        rfl
      · rw [dif_neg b, if_neg (show ¬ i'.1 + 1 ≤ _ from b), hB _ (by omega), Int.cast_neg,
          show i'.1 + 1 - (X.B.R.k - 1) = i'.1 - (X.B.R.k - 1) + 1 by omega]
        rfl
    · rw [if_neg a, if_neg (show ¬ i'.1 + 1 ≤ _ from a)]
      by_cases b : i'.1 < X.B.R.k + j - 1 + X.B.R.t
      · rw [if_pos b, if_pos (show i'.1 + 1 ≤ _ from b)]
      · rw [if_neg b, if_neg (show ¬ i'.1 + 1 ≤ _ from b), hB _ (by omega),
          show X.B.R.m - j + 1 - (X.B.R.m - j + 1 - (i'.1 + 1 - (X.B.R.k + j - 1) - X.B.R.t)) =
            i'.1 - (X.B.R.k + j - 1 + X.B.R.t) + 1 by omega,
          show j + (i'.1 - (X.B.R.k + j - 1 + X.B.R.t) + 1) - 1 + 1 = j + (i'.1 - (X.B.R.k + j - 1 + X.B.R.t) + 1) by omega]
  have := (hw i).trans ((e ▸ key).trans q.symm)
  exact_mod_cast this

theorem gram_X' (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hI : I.Ok) : X.toD7.sp.X'.gram = 1 := by
  obtain ⟨hs, -, h2, -⟩ := hI.spaces
  change X.B.sp.X'.gram = 1
  rw [h2]
  refine Matrix.ext fun i i' => (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply hs _ _ _ _ i i').trans ?_
  simp [Matrix.one_apply, Formalism.BasicNotions.Examples₂.sgn]

theorem gram_V (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hI : I.Ok) (i : Fin X.toD7.R.m) : (Vc X.toD7 i).gram = 1 := by
  obtain ⟨hs, -, -, -, -, hV⟩ := hI.spaces
  have h1 := hV ((i : ℕ) + 1)
  have hn : X.B.sp.Vneg ((i : ℕ) + 1) = false := X.B.V_pos _ (by omega) i.2
  rw [hn] at h1
  change (X.B.sp.V ((i : ℕ) + 1)).gram = 1
  rw [h1]
  refine Matrix.ext fun a b => (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply hs _ _ _ _ a b).trans ?_
  simp [Matrix.one_apply, Formalism.BasicNotions.Examples₂.sgn]

theorem matEq_unique {A : Type} [CommRing A] {a b : ℕ} {x : GL (Fin a) A} {y y' : GL (Fin b) A} (h : MatEq x y) (h' : MatEq x y') :
    y = y' := by
  obtain rfl := h.1
  exact (eq_of_matEq h).symm.trans (eq_of_matEq h')

variable (X : Stages) {px : PreX X.B.toPre} (I : ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL))
  (tr : TrI X.B px)

set_option maxHeartbeats 4000000 in

theorem exists_brgStdV (hI : I.Ok) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (i : Fin X.toD7.R.m) (hβ : L.βV i = 1) :
    ∃ cV : CoefA (Vc X.toD7 i), cV.Is ∧ ∃ jL, BrgStdV X I hX U Xg tr L i cV jL := by
  obtain ⟨cV, c0, hIs, hT, -⟩ := GlobalTheory.CoefModel.exists_coef_lift X.toD7 i (X.B.V_posDef _ (by omega) i.2)
  have hr : (Vc X.toD7 i).rank = X.B.R.nV := X.toD7.sp.V_rank _ (by omega) i.2
  obtain ⟨c, hc, hli⟩ := transport (W := cV.W) (K := X.toD7.what₂.LL) (E := X.toD7.host.E) (ι' := X.toD7.what₂.Tau) X.toD7.what₂.embLL hr _
    (X.B.wts.lamV ((i : ℕ) + 1)) (fun τ a a' e => lamLdef_eq X ((i : ℕ) + 1) (by omega) i.2 τ a a' e)
    (fun l => rhoVr (labLL X.toD7) l) c0 hT.2.1 (Bridge.IsRatMat (Vc X.toD7 i)) (fun γ v => cV.coef.ρ γ v) hT.1
  choose x hx using exists_matEq (D := X.toD7) (Vc X.toD7 i) hr (gram_V X I hI i)
  refine ⟨cV, hIs, fun t f h => c ((((mtKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).res
    (mtKOk _ _ _ _ hX _)).symm f).1 (decoPt (F := X.toD7.host.F) (E := X.toD7.host.E) X.toD7.sp.cm X.B.R.nV ∅ (rowSG (X.B.primes px) I.sel t.1) (QuotientGroup.mk (x h)))), ?_⟩
  unfold BrgStdV StdSide
  rw [hβ]
  refine ⟨c, hc, ?_, hli, X.toD7.sp.cm, fun h => ⟨x h, hx h⟩⟩
  intro hc' t φ h y hm
  obtain rfl : x h = y := Subtype.ext (matEq_unique (hx h) hm)
  exact congrArg (fun g : (mtKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1 ((i : ℕ) + 1)).EqFun => c (g.1 _))
    (LinearEquiv.symm_apply_apply _ φ.2)

open Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Indef in
set_option maxHeartbeats 4000000 in

theorem exists_brgStdR (hI : I.Ok) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (hβ : L.βX = 1) (θ : InfFam X.toD7) (hθ : IsInfFam θ)
    (M : DSModel X.toD7.sp.X' (parB (Ptw X.toD7) X.toD7.R.m)) :
    ∃ cX : CoefA X.toD7.sp.X', cX.Is ∧ ∃ jR, BrgStdR X I hX U Xg tr L cX jR := by
  obtain ⟨cX, pr, c0, gr, hIs, -, -, hT, -⟩ := GlobalTheory.CoefSpace.exists_coef_dualPair X.toD7 θ M hθ
  have hr : X.toD7.sp.X'.rank = X.B.R.N X.B.R.m - 1 := by rw [X.toD7.sp.X'_rank, rank_X'_eq]; rfl
  obtain ⟨c, hc, hli⟩ := transport (W := cX.W) (K := X.toD7.what₂.LL) (E := X.toD7.host.E) (ι' := X.toD7.what₂.Tau) X.toD7.what₂.embLL hr _
    X.B.wts.sgTrue (fun τ a a' e => lamRdef_eq X τ a a' e)
    (fun l => rhoV (labLL X.toD7) l) c0 hT.2.1 (Bridge.IsRatMat X.toD7.sp.X') (fun γ v => cX.coef.ρ γ v) hT.1
  choose x hx using exists_matEq (D := X.toD7) X.toD7.sp.X' hr (gram_X' X I hI)
  refine ⟨cX, hIs, fun t f h => c ((((mtildeKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1).res
    (mtildeKOk _ _ _ _ hX)).symm f).1 (decoPt (F := X.toD7.host.F) (E := X.toD7.host.E) X.toD7.sp.cm (X.B.R.N X.B.R.m - 1) ∅ (rowSG (X.B.primes px) I.sel t.1) (QuotientGroup.mk (x h)))), ?_⟩
  unfold BrgStdR StdSide
  rw [hβ]
  refine ⟨c, hc, ?_, hli, X.toD7.sp.cm, fun h => ⟨x h, hx h⟩⟩
  intro hc' t φ h y hm
  obtain rfl : x h = y := Subtype.ext (matEq_unique (hx h) hm)
  exact congrArg (fun g : (mtildeKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1).EqFun => c (g.1 _))
    (LinearEquiv.symm_apply_apply _ φ.2)

end Rec

end GlobalTheory.Mem.R3.StdModel

end
