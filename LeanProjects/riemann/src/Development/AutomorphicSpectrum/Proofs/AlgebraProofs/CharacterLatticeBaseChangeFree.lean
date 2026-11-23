import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocFreeMapMkQIff
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeGoodBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeBaseChangeQuotientStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SmulMemSpanOver
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Imports

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.KerBC

open GlobalTheory.CompanionTheory.Ar.Num

section Swap

variable {o Ω C : Type} [CommRing o] [Field Ω] [Field C] [Algebra o Ω] [Algebra o C] [Algebra Ω C]
  [IsScalarTower o Ω C] (R : Subalgebra o Ω) (RC : Subalgebra o C)
  (hR : ∀ a ∈ R, algebraMap Ω C a ∈ RC)
  {V Vc : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup Vc] [Module C Vc] [Module Ω Vc]
  [IsScalarTower Ω C Vc]
  {Z Zc : Type} [AddCommGroup Z] [Module Ω Z] [AddCommGroup Zc] [Module C Zc] [Module Ω Zc]
  [IsScalarTower Ω C Zc]
  (b : V →ₗ[Ω] Vc) (b' : Z →ₗ[Ω] Zc)

abbrev swp (Γ : AddSubgroup (V × Z)) : AddSubgroup (Z × V) :=
  Γ.map (AddEquiv.prodComm (M := V) (N := Z)).toAddMonoidHom

omit [Module Ω V] [Module Ω Z] in
theorem mem_swp {Γ : AddSubgroup (V × Z)} {u : Z} {v : V} : (u, v) ∈ swp Γ ↔ (v, u) ∈ Γ := by
  constructor
  · rintro ⟨⟨x, y⟩, h, e⟩
    have e' : (y, x) = (u, v) := e
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj e'
    exact h
  · intro h
    exact ⟨(v, u), h, rfl⟩

omit [Module Ω V] [Module Ω Z] in
theorem map_fst_swp (Γ : AddSubgroup (V × Z)) :
    (swp Γ).map (AddMonoidHom.fst Z V) = Γ.map (AddMonoidHom.snd V Z) := by
  ext x
  constructor
  · rintro ⟨⟨u, v⟩, h, rfl⟩
    exact ⟨(v, u), mem_swp.1 h, rfl⟩
  · rintro ⟨⟨u, v⟩, h, rfl⟩
    exact ⟨(v, u), mem_swp.2 h, rfl⟩

theorem swp_stable {Γ : AddSubgroup (V × Z)} (hs : ∀ a ∈ R, ∀ v ∈ Γ, a • v ∈ Γ) :
    ∀ a ∈ R, ∀ v ∈ swp Γ, a • v ∈ swp Γ := by
  rintro a ha ⟨u, v⟩ h
  have := hs a ha _ (mem_swp.1 h)
  exact mem_swp.2 this

include hR in

theorem comap_inl (hb : IsBaseChange C b) (hb' : IsBaseChange C b')
    (Γ : AddSubgroup (V × Z)) (N : ℕ) (hs : ∀ a ∈ R, ∀ v ∈ Γ, a • v ∈ Γ)
    (hf : LocFree R N (Γ.map (AddMonoidHom.snd V Z))) :
    (spanOver RC (Prod.map b b' '' Γ)).comap (AddMonoidHom.inl Vc Zc) =
      spanOver RC (b '' Γ.comap (AddMonoidHom.inl V Z)) := by
  have key := (GlobalTheory.T.locally_free_base_change_quotient R RC hR b' b hb' hb (swp Γ) ⊥ N (swp_stable R hs)
    (by rw [map_fst_swp]; exact hf) bot_le
    (by
      intro a _ v hv
      rw [AddSubgroup.mem_bot] at hv ⊢
      rw [hv, smul_zero])).2
  have hcom : (swp Γ).comap (AddMonoidHom.inr Z V) = Γ.comap (AddMonoidHom.inl V Z) := by
    ext x
    simp only [AddSubgroup.mem_comap, AddMonoidHom.inr_apply, AddMonoidHom.inl_apply]
    exact mem_swp
  rw [hcom, spanOver_swap RC b' b Γ] at key
  rw [← key]
  ext x
  simp only [AddSubgroup.mem_comap, AddMonoidHom.inr_apply, AddMonoidHom.inl_apply]
  exact (mem_swp (Γ := spanOver RC (Prod.map b b' '' Γ))).symm

include hR in

theorem inf_top_prod (hb : IsBaseChange C b) (hb' : IsBaseChange C b')
    (Γ : AddSubgroup (V × Z)) (H : AddSubgroup Z) (N : ℕ) (hs : ∀ a ∈ R, ∀ v ∈ Γ, a • v ∈ Γ)
    (hf : LocFree R N (Γ.map (AddMonoidHom.snd V Z))) (hle : H ≤ Γ.map (AddMonoidHom.snd V Z))
    (hH : ∀ a ∈ R, ∀ v ∈ H, a • v ∈ H) :
    spanOver RC (Prod.map b b' '' Γ) ⊓ (⊤ : AddSubgroup Vc).prod (spanOver RC (b' '' H)) =
      spanOver RC (Prod.map b b' '' (Γ ⊓ (⊤ : AddSubgroup V).prod H : AddSubgroup (V × Z))) := by
  have key := (GlobalTheory.T.locally_free_base_change_quotient R RC hR b' b hb' hb (swp Γ) H N (swp_stable R hs)
    (by rw [map_fst_swp]; exact hf) (by rw [map_fst_swp]; exact hle) hH).1
  have hres : swp Γ ⊓ H.prod (⊤ : AddSubgroup V) =
      swp (Γ ⊓ (⊤ : AddSubgroup V).prod H : AddSubgroup (V × Z)) := by
    ext ⟨u, v⟩
    rw [mem_swp]
    simp only [AddSubgroup.mem_inf, AddSubgroup.mem_prod, AddSubgroup.mem_top, and_true, true_and]
    rw [mem_swp]
  rw [hres, spanOver_swap RC b' b Γ, spanOver_swap RC b' b] at key
  ext ⟨x, y⟩
  have := SetLike.ext_iff.1 key (y, x)
  simp only [AddSubgroup.mem_inf, AddSubgroup.mem_prod, AddSubgroup.mem_top, and_true, true_and] at this ⊢
  rw [mem_swp (Γ := spanOver RC (Prod.map b b' '' Γ)),
    mem_swp (Γ := spanOver RC (Prod.map b b' '' _))] at this
  exact this

end Swap

section Core

variable {o Ω C : Type} [CommRing o] [Field Ω] [Field C] [Algebra o Ω] [Algebra o C] [Algebra Ω C]
  [IsScalarTower o Ω C] (R : Subalgebra o Ω) (RC : Subalgebra o C)
  (hR : ∀ a ∈ R, algebraMap Ω C a ∈ RC)
  {A Ac : Type} [AddCommGroup A] [Module Ω A] [AddCommGroup Ac] [Module C Ac] [Module Ω Ac]
  [IsScalarTower Ω C Ac]
  {B Bc : Type} [AddCommGroup B] [Module Ω B] [AddCommGroup Bc] [Module C Bc] [Module Ω Bc]
  [IsScalarTower Ω C Bc]
  {S Sc : Type} [AddCommGroup S] [Module Ω S] [AddCommGroup Sc] [Module C Sc] [Module Ω Sc]
  [IsScalarTower Ω C Sc]
  (a : A →ₗ[Ω] Ac) (b : B →ₗ[Ω] Bc) (c : S →ₗ[Ω] Sc)

include hR in

theorem core (ha : IsBaseChange C a) (hb : IsBaseChange C b) (hc : IsBaseChange C c)
    (Gam : AddSubgroup (A × B)) (Del : AddSubgroup (B × S)) (hh : AddSubgroup B) (n₁ n₂ n₃ : ℕ)
    (hGs : ∀ x ∈ R, ∀ v ∈ Gam, x • v ∈ Gam) (hDs : ∀ x ∈ R, ∀ v ∈ Del, x • v ∈ Del)
    (hhs : ∀ x ∈ R, ∀ v ∈ hh, x • v ∈ hh)
    (f₁ : LocFree R n₁ (Del.map (AddMonoidHom.fst B S)))
    (hle : hh ≤ Del.map (AddMonoidHom.fst B S))
    (f₂ : LocFree R n₂ ((Del ⊓ hh.prod (⊤ : AddSubgroup S) : AddSubgroup (B × S)).map
      (AddMonoidHom.snd B S)))
    (f₃ : LocFree R n₂ (Del.map (AddMonoidHom.snd B S)))
    (f₄ : LocFree R n₃ (Gam.map (AddMonoidHom.snd A B)))
    (hGD : Gam.map (AddMonoidHom.snd A B) = Del.comap (AddMonoidHom.inl B S)) :
    (spanOver RC (Prod.map a b '' Gam) ⊓
        (⊤ : AddSubgroup Ac).prod (spanOver RC (b '' hh))).map (AddMonoidHom.fst Ac Bc) =
      spanOver RC (a '' (Gam ⊓ (⊤ : AddSubgroup A).prod hh : AddSubgroup (A × B)).map
        (AddMonoidHom.fst A B)) := by
  set T : AddSubgroup (B × S) := Del ⊓ hh.prod (⊤ : AddSubgroup S) with hT
  set K : AddSubgroup B := T.comap (AddMonoidHom.inl B S) with hK
  have hTs : ∀ x ∈ R, ∀ v ∈ T, x • v ∈ T := by
    rintro x hx ⟨u, v⟩ h
    obtain ⟨h1, h2⟩ := AddSubgroup.mem_inf.1 h
    refine AddSubgroup.mem_inf.2 ⟨hDs x hx _ h1, ?_⟩
    exact AddSubgroup.mem_prod.2 ⟨hhs x hx _ (AddSubgroup.mem_prod.1 h2).1, AddSubgroup.mem_top _⟩
  have hKs : ∀ x ∈ R, ∀ v ∈ K, x • v ∈ K := by
    intro x hx v hv
    have := hTs x hx _ hv
    simpa [hK] using this
  have hKhh : K ≤ hh := fun v hv => (AddSubgroup.mem_prod.1 (AddSubgroup.mem_inf.1 hv).2).1
  have hKG : K ≤ Gam.map (AddMonoidHom.snd A B) := by
    rw [hGD]
    exact fun v hv => (AddSubgroup.mem_inf.1 hv).1
  have e1 := (GlobalTheory.T.locally_free_base_change_quotient R RC hR b c hb hc Del hh n₁ hDs f₁ hle hhs).1
  have e2 := comap_inl R RC hR b c hb hc T n₂ hTs f₂
  have e3 := comap_inl R RC hR b c hb hc Del n₂ hDs f₃
  have e4 : (spanOver RC (Prod.map a b '' Gam)).map (AddMonoidHom.snd Ac Bc) =
      spanOver RC (b '' Gam.map (AddMonoidHom.snd A B)) := by
    have := SpanExact.map_spanOver RC (Prod.map a b '' (Gam : Set (A × B))) (LinearMap.snd C Ac Bc)
    refine Eq.trans this ?_
    congr 1
    ext y
    constructor
    · rintro ⟨_, ⟨⟨u, v⟩, h, rfl⟩, rfl⟩
      exact ⟨v, ⟨(u, v), h, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨⟨u, v⟩, h, rfl⟩, rfl⟩
      exact ⟨_, ⟨(u, v), h, rfl⟩, rfl⟩
  have e5 := inf_top_prod R RC hR a b ha hb Gam K n₃ hGs f₄ hKG hKs
  have hspan : spanOver RC (b '' K) ≤ spanOver RC (b '' hh) := by
    refine AddSubgroup.closure_mono ?_
    rintro _ ⟨x, hx, e, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨x, hx, _, ⟨v, hKhh hv, rfl⟩, rfl⟩
  have e6 : spanOver RC (Prod.map a b '' Gam) ⊓
      (⊤ : AddSubgroup Ac).prod (spanOver RC (b '' hh)) =
      spanOver RC (Prod.map a b '' Gam) ⊓ (⊤ : AddSubgroup Ac).prod (spanOver RC (b '' K)) := by
    ext ⟨x, y⟩
    simp only [AddSubgroup.mem_inf, AddSubgroup.mem_prod, AddSubgroup.mem_top, true_and]
    refine ⟨fun ⟨h1, h2⟩ => ⟨h1, ?_⟩, fun ⟨h1, h2⟩ => ⟨h1, hspan h2⟩⟩
    have h3 : y ∈ (spanOver RC (Prod.map a b '' Gam)).map (AddMonoidHom.snd Ac Bc) :=
      ⟨(x, y), h1, rfl⟩
    rw [e4, hGD, ← e3] at h3
    have h4 : (y, (0 : Sc)) ∈ spanOver RC (Prod.map b c '' Del) ⊓
        (spanOver RC (b '' hh)).prod (⊤ : AddSubgroup Sc) :=
      AddSubgroup.mem_inf.2 ⟨h3, AddSubgroup.mem_prod.2 ⟨h2, AddSubgroup.mem_top _⟩⟩
    rw [e1] at h4
    rw [← e2]
    exact h4
  have e7 : (Gam ⊓ (⊤ : AddSubgroup A).prod K : AddSubgroup (A × B)) =
      Gam ⊓ (⊤ : AddSubgroup A).prod hh := by
    ext ⟨x, y⟩
    simp only [AddSubgroup.mem_inf, AddSubgroup.mem_prod, AddSubgroup.mem_top, true_and]
    refine ⟨fun ⟨h1, h2⟩ => ⟨h1, hKhh h2⟩, fun ⟨h1, h2⟩ => ⟨h1, ?_⟩⟩
    have h3 : y ∈ Gam.map (AddMonoidHom.snd A B) := ⟨(x, y), h1, rfl⟩
    rw [hGD] at h3
    exact AddSubgroup.mem_inf.2 ⟨h3, AddSubgroup.mem_prod.2 ⟨h2, AddSubgroup.mem_top _⟩⟩
  rw [e6, e5, e7]
  have := SpanExact.map_spanOver RC
    (Prod.map a b '' ((Gam ⊓ (⊤ : AddSubgroup A).prod hh : AddSubgroup (A × B)) : Set (A × B)))
    (LinearMap.fst C Ac Bc)
  refine Eq.trans this ?_
  congr 1
  ext y
  constructor
  · rintro ⟨_, ⟨⟨u, v⟩, h, rfl⟩, rfl⟩
    exact ⟨u, ⟨(u, v), h, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨⟨u, v⟩, h, rfl⟩, rfl⟩
    exact ⟨_, ⟨(u, v), h, rfl⟩, rfl⟩

end Core

theorem smul_mem_stdLat_of_mem_hh {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type}
    [Zero F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s)
    (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : F → Ω)
    (hw : mulLat w (stdLat R _) ≤ D.af R p χ) {v : Fin n → Ω} (hv : v ∈ D.hh R p χ) :
    w • v ∈ stdLat R _ := by
  classical
  rw [mem_stdLat]
  intro j
  have h1 : (Pi.single j 1 : Fin n → Ω) ∈ stdLat R (Fin n) := by
    rw [mem_stdLat]
    intro k
    rw [Pi.single_apply]
    split_ifs
    · exact R.one_mem
    · exact R.zero_mem
  have hl : w • (Pi.single j 1 : Fin n → Ω) ∈ D.af R p χ := hw ⟨_, h1, rfl⟩
  unfold LieLatticeData.hh dotDual at hv
  simp only [AddSubgroup.mem_iInf] at hv
  have h2 : (w • (Pi.single j 1 : Fin n → Ω)) ⬝ᵥ v ∈ R := hv _ hl
  have h3 : (w • (Pi.single j 1 : Fin n → Ω)) ⬝ᵥ v = (w • v) j := by
    simp [smul_dotProduct, single_one_dotProduct]
  rwa [h3] at h2

theorem main : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → D.Good₁ R p χ → D.Good₂ R p χ → (∀ τ, mulLat w (stdLat R _) ≤ D.af R p (χ τ)) → ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ τ, (D.bc RC).kerH RC p τ (fun a => algebraMap Ω C (χ τ a)) = spanOver RC (bcMap Ω C _ '' D.kerH R p τ (χ τ)) := by
  intro o Ω _ _ _ F _ _ _ n Sg r s D R p w χ hcd hB hG₁ hG₂ hw C _ _ _ _ RC hR τ
  obtain ⟨h1a, h1b⟩ := GlobalTheory.T.lattice_good_base_change D R p w χ hcd hB hG₁
  have hhh := (h1b C RC hR).2 τ |>.2.1
  have hw0 : w ≠ 0 := by
    rintro rfl
    obtain ⟨hp, -, ⟨c, -, hc⟩, -⟩ := hcd
    exact hp (by simpa using hc)
  have hhfree : LocFree R n (D.hh R p (χ τ)) := (h1a τ).2.1
  obtain ⟨hdF, hdS, hd0, hdG⟩ := hB.del τ
  obtain ⟨-, -, -, hOm⟩ := hB.free τ
  have hGs := (fun x hx => (hB.stable τ x hx).1)
  have hDs := (fun x hx => (hB.stable τ x hx).2.1)
  have eF : (D.Del τ).map (AddMonoidHom.fst _ _) = divLat w (stdLat R (Fin n)) := by
    ext v
    constructor
    · rintro ⟨⟨x, y⟩, h, rfl⟩
      exact (hdF x).1 ⟨y, h⟩
    · intro hv
      obtain ⟨y, hy⟩ := (hdF v).2 hv
      exact ⟨(v, y), hy, rfl⟩
  have eS : (D.Del τ).map (AddMonoidHom.snd _ _) = divLat w (D.omHT τ) := by
    ext v
    constructor
    · rintro ⟨⟨x, y⟩, h, rfl⟩
      exact (hdS y).1 ⟨x, h⟩
    · intro hv
      obtain ⟨y, hy⟩ := (hdS v).2 hv
      exact ⟨(y, v), hy, rfl⟩
  have hGD : (D.Gam τ).map (AddMonoidHom.snd _ _) = (D.Del τ).comap (AddMonoidHom.inl _ _) := by
    ext v
    constructor
    · rintro ⟨⟨x, y⟩, h, rfl⟩
      exact (hdG y).2 ⟨x, h⟩
    · intro hv
      obtain ⟨y, hy⟩ := (hdG v).1 hv
      exact ⟨(y, v), hy, rfl⟩
  have hG2 : LocFree R n ((D.Gam τ).map (AddMonoidHom.snd _ _)) := by
    rw [hGD]
    refine (LocFreeSchanuel.main R n (s τ) (divLat w (stdLat R (Fin n))) (divLat w (D.omHT τ)) (D.omHT τ)
      (D.Del τ) (LatticeGoodness.locFree_divLat R hw0 (LatticeGoodness.locFree_stdLat R n))
      (LatticeGoodness.locFree_divLat R hw0 hOm) hOm hDs ?_ ?_ hd0 ?_).2
    · intro v y h
      exact ⟨(hdF v).1 ⟨y, h⟩, (hdS y).1 ⟨v, h⟩⟩
    · exact fun v hv => (hdF v).2 hv
    · exact fun y hy => (hdS y).2 hy
  have hle : D.hh R p (χ τ) ≤ (D.Del τ).map (AddMonoidHom.fst _ _) := by
    rw [eF]
    exact fun v hv => smul_mem_stdLat_of_mem_hh D R p w (χ τ) (hw τ) hv
  have key := core R RC hR (bcMap Ω C (Fin (r τ))) (bcMap Ω C (Fin n)) (bcMap Ω C (Fin (s τ)))
    (LatticeGoodness.isBaseChange_bcMap Ω C _) (LatticeGoodness.isBaseChange_bcMap Ω C _)
    (LatticeGoodness.isBaseChange_bcMap Ω C _) (D.Gam τ) (D.Del τ) (D.hh R p (χ τ)) n (s τ) n hGs hDs hhfree.1
    (by rw [eF]; exact LatticeGoodness.locFree_divLat R hw0 (LatticeGoodness.locFree_stdLat R n)) hle (hG₂.im τ)
    (by rw [eS]; exact LatticeGoodness.locFree_divLat R hw0 hOm) hG2 hGD
  unfold LieLatticeData.kerH
  rw [hhh]
  exact key

end GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.KerBC
