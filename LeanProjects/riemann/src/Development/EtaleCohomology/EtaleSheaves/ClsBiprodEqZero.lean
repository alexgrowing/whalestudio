import Development.EtaleCohomology.EtaleSheaves.ProdAcycPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.BinPf

universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]

theorem cls_biprod_eq_zero {K₁ K₂ L : CochainComplex C ℤ} {n : ℤ} (x : CohomologyClass (K₁ ⊞ K₂) L n)
    (h₁ : cpre (Cocycle.ofHom (biprod.inl : K₁ ⟶ K₁ ⊞ K₂)) L n n (zero_add n) x = 0)
    (h₂ : cpre (Cocycle.ofHom (biprod.inr : K₂ ⟶ K₁ ⊞ K₂)) L n n (zero_add n) x = 0) : x = 0 := by
  obtain ⟨α, rfl⟩ := x.mk_surjective
  rw [cpre_mk, CohomologyClass.mk_eq_zero_iff] at h₁ h₂
  obtain ⟨m, hm, β₁, hβ₁⟩ := h₁
  obtain ⟨m', hm', β₂, hβ₂⟩ := h₂
  have hmm : m' = m := by omega
  subst hmm
  rw [CohomologyClass.mk_eq_zero_iff]
  refine ⟨m', hm', (Cochain.ofHom (biprod.fst : K₁ ⊞ K₂ ⟶ K₁)).comp β₁ (zero_add m') +
    (Cochain.ofHom (biprod.snd : K₁ ⊞ K₂ ⟶ K₂)).comp β₂ (zero_add m'), ?_⟩
  rw [δ_add, δ_ofHom_comp, δ_ofHom_comp, hβ₁, hβ₂]
  change (Cochain.ofHom (biprod.fst : K₁ ⊞ K₂ ⟶ K₁)).comp ((Cochain.ofHom biprod.inl).comp α.1 (zero_add n)) (zero_add n) +
    (Cochain.ofHom (biprod.snd : K₁ ⊞ K₂ ⟶ K₂)).comp ((Cochain.ofHom biprod.inr).comp α.1 (zero_add n)) (zero_add n) = α.1
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.comp_assoc_of_first_is_zero_cochain,
    ← Cochain.add_comp, ← Cochain.ofHom_comp, ← Cochain.ofHom_comp, ← Cochain.ofHom_add, biprod.total,
    Cochain.id_comp]

theorem hkpull_comp {R : Type} [CommRing R] {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (F : Shv R) (n : ℤ)
    (x : HK R M F n) : HK.pull R (f ≫ g) F n x = HK.pull R f F n (HK.pull R g F n x) := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [HK.pull, HK.pre, cpre_mk, zcomp, Cochain.ofHom_comp]

theorem hkpull_id {R : Type} [CommRing R] {K : Cx R} (F : Shv R) (n : ℤ)
    (x : HK R K F n) : HK.pull R (𝟙 K) F n x = x := by
  obtain ⟨x, rfl⟩ := x.mk_surjective
  refine congrArg CohomologyClass.mk (Cocycle.ext ?_)
  simp [HK.pull, HK.pre, cpre_mk, zcomp]

def ChainsCoprod : Prop := ∀ (R : Type) [CommRing R] (U V : Spc),
  IsIso (biprod.desc ((chains R).map (coprod.inl : U ⟶ U ⨿ V)) ((chains R).map (coprod.inr : V ⟶ U ⨿ V)))

def CoprodAcyc : Prop := ∀ (q : ℕ) (U V : Spc), Acyc q U → Acyc q V → Acyc q (U ⨿ V)

theorem coprodAcyc_of (hC : ChainsCoprod) : CoprodAcyc := by
  intro q U V hU hV n i hn
  have hI := hC (ZMod q) U V
  set φ := biprod.desc ((chains (ZMod q)).map (coprod.inl : U ⟶ U ⨿ V)) ((chains (ZMod q)).map (coprod.inr : V ⟶ U ⨿ V))
  have h0 : ∀ x : Ht q (U ⨿ V) n i, x = 0 := by
    intro x
    have hy : HK.pull _ φ _ n x = 0 := by
      apply cls_biprod_eq_zero
      · have e := hkpull_comp (biprod.inl) φ (tw q i) n x
        rw [biprod.inl_desc] at e
        have : HK.pull _ ((chains (ZMod q)).map (coprod.inl : U ⟶ U ⨿ V)) (tw q i) n x = 0 :=
          (hU n i hn).elim _ _
        rw [this] at e
        exact e.symm
      · have e := hkpull_comp (biprod.inr) φ (tw q i) n x
        rw [biprod.inr_desc] at e
        have : HK.pull _ ((chains (ZMod q)).map (coprod.inr : V ⟶ U ⨿ V)) (tw q i) n x = 0 :=
          (hV n i hn).elim _ _
        rw [this] at e
        exact e.symm
    have e := hkpull_comp (inv φ) φ (tw q i) n x
    rw [IsIso.inv_hom_id, hkpull_id, hy, map_zero] at e
    exact e
  exact ⟨fun x y => by rw [h0 x, h0 y]⟩

def DescEqv : Prop := LateralTheory.E.t_E2Cut.Hyp → ∀ (q : ℕ) (A R0 R1 : Type) [CommRing A] [CommRing R0] [CommRing R1]
  (e : A ≃+* R0 × R1) (i : ℤ),
  Eqv _ (coprod.desc (spMap ((RingHom.fst R0 R1).comp e.toRingHom)) (spMap ((RingHom.snd R0 R1).comp e.toRingHom))) (tw q i)

end LateralTheory.E.BinPf

theorem LateralTheory.E.ProdAcycPf.Bin_of (hD : LateralTheory.E.BinPf.DescEqv) (hC : LateralTheory.E.BinPf.ChainsCoprod) :
    LateralTheory.E.ProdAcycPf.Bin := by
  intro H q A R0 R1 _ _ _ ⟨e⟩ h0 h1 n i hn
  have hb := (hD H q A R0 R1 e i n).1
  have hs := LateralTheory.E.BinPf.coprodAcyc_of hC q _ _ h0 h1 n i hn
  exact ⟨fun x y => hb (Subsingleton.elim _ _)⟩
