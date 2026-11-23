import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSpMapEv

open AlgebraicGeometry CategoryTheory TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)

noncomputable section
namespace GlobalTheory.FlagMod.FieldFlag.Glue

private theorem exists_pow_smul_mem_of_mem_span_away' {R : Type} [CommRing R] (r : R) {n : ℕ} (N : Submodule R (Fin n → R))
    (x : Fin n → R)
    (hx : (fun t => algebraMap R (Localization.Away r) (x t)) ∈
      Submodule.span (Localization.Away r)
        ((fun (y : Fin n → R) t => algebraMap R (Localization.Away r) (y t)) '' (N : Set (Fin n → R)))) :
    ∃ k : ℕ, r ^ k • x ∈ N := by
  have key : ∀ y ∈ Submodule.span (Localization.Away r)
      ((fun (y : Fin n → R) t => algebraMap R (Localization.Away r) (y t)) '' (N : Set (Fin n → R))),
      ∃ m ∈ N, ∃ k : ℕ, (algebraMap R (Localization.Away r) r) ^ k • y =
        fun t => algebraMap R (Localization.Away r) (m t) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨m, hm, rfl⟩ := hy
      exact ⟨m, hm, 0, by simp⟩
    | zero => exact ⟨0, N.zero_mem, 0, by funext t; simp⟩
    | add y₁ y₂ _ _ h₁ h₂ =>
      obtain ⟨m₁, hm₁, k₁, e₁⟩ := h₁
      obtain ⟨m₂, hm₂, k₂, e₂⟩ := h₂
      refine ⟨r ^ k₂ • m₁ + r ^ k₁ • m₂, N.add_mem (N.smul_mem _ hm₁) (N.smul_mem _ hm₂), k₁ + k₂, ?_⟩
      funext t
      have e₁t := congrFun e₁ t
      have e₂t := congrFun e₂ t
      simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, map_add, map_mul, map_pow] at e₁t e₂t ⊢
      rw [← e₁t, ← e₂t]
      ring
    | smul a y _ h =>
      obtain ⟨m, hm, k, e⟩ := h
      obtain ⟨⟨b, d⟩, hab⟩ := IsLocalization.surj (Submonoid.powers r) a
      obtain ⟨q, hq⟩ := (Submonoid.mem_powers_iff _ _).mp d.2
      refine ⟨b • m, N.smul_mem _ hm, k + q, ?_⟩
      funext t
      have et := congrFun e t
      simp only [Pi.smul_apply, smul_eq_mul, map_mul] at et hab ⊢
      rw [← hq, map_pow] at hab
      rw [← et, ← hab]
      ring
  obtain ⟨m, hm, k, e⟩ := key _ hx
  have ht : ∀ t, ∃ q : ℕ, r ^ q * (r ^ k * x t) = r ^ q * m t := by
    intro t
    have et := congrFun e t
    simp only [Pi.smul_apply, smul_eq_mul] at et
    rw [← map_pow, ← map_mul] at et
    obtain ⟨c, hc⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers r) et
    obtain ⟨q, hq⟩ := (Submonoid.mem_powers_iff _ _).mp c.2
    exact ⟨q, by rw [hq]; exact hc⟩
  choose q hq using ht
  refine ⟨(∑ t, q t) + k, ?_⟩
  have hx' : r ^ ((∑ t, q t) + k) • x = r ^ (∑ t, q t) • m := by
    funext t
    simp only [Pi.smul_apply, smul_eq_mul]
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le
      (Finset.single_le_sum (f := q) (fun _ _ => Nat.zero_le _) (Finset.mem_univ t))
    rw [hd]
    calc r ^ (q t + d + k) * x t = r ^ d * (r ^ q t * (r ^ k * x t)) := by ring
      _ = r ^ d * (r ^ q t * m t) := by rw [hq t]
      _ = r ^ (q t + d) * m t := by ring
  rw [hx']
  exact N.smul_mem _ hm

theorem initSpan_le_of_away {R : Type} [CommRing R] {ι : Type} (s : ι → R) (hs : Ideal.span (Set.range s) = ⊤)
    {m n : ℕ} (u v : Fin m → Fin n → R) (j : ℕ)
    (h : ∀ i, initSpan (Localization.Away (s i)) (fun a t => algebraMap R (Localization.Away (s i)) (u a t)) j ≤
      initSpan (Localization.Away (s i)) (fun a t => algebraMap R (Localization.Away (s i)) (v a t)) j) :
    initSpan R u j ≤ initSpan R v j := by
  unfold initSpan at *
  rw [Submodule.span_le]
  rintro _ ⟨a, ha, rfl⟩
  apply Submodule.mem_of_span_eq_top_of_smul_pow_mem _ (Set.range s) hs
  rintro ⟨_, ⟨i, rfl⟩⟩
  apply exists_pow_smul_mem_of_mem_span_away' (s i)
  have hmem : (fun t => algebraMap R (Localization.Away (s i)) (u a t)) ∈
      Submodule.span (Localization.Away (s i))
        ((fun a t => algebraMap R (Localization.Away (s i)) (v a t)) '' {b : Fin m | (b : ℕ) < j}) :=
    h i (Submodule.subset_span ⟨a, ha, rfl⟩)
  refine Submodule.span_mono ?_ hmem
  rintro _ ⟨b, hb, rfl⟩
  exact ⟨v b, Submodule.subset_span ⟨b, hb, rfl⟩, rfl⟩

theorem initSpan_eq_of_away {R : Type} [CommRing R] {ι : Type} (s : ι → R) (hs : Ideal.span (Set.range s) = ⊤)
    {m n : ℕ} (u v : Fin m → Fin n → R) (j : ℕ)
    (h : ∀ i, initSpan (Localization.Away (s i)) (fun a t => algebraMap R (Localization.Away (s i)) (u a t)) j =
      initSpan (Localization.Away (s i)) (fun a t => algebraMap R (Localization.Away (s i)) (v a t)) j) :
    initSpan R u j = initSpan R v j :=
  le_antisymm (initSpan_le_of_away s hs u v j fun i => (h i).le)
    (initSpan_le_of_away s hs v u j fun i => (h i).ge)

theorem ext_away {S : Type} [CommRing S] {X : Scheme.{0}} {ι : Type} (f : ι → S)
    (hf : Ideal.span (Set.range f) = ⊤) {w w' : Sp S ⟶ X}
    (h : ∀ i, spMap (algebraMap S (Localization.Away (f i))) ≫ w = spMap (algebraMap S (Localization.Away (f i))) ≫ w') :
    w = w' :=
  Scheme.Cover.hom_ext (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of S) f hf).openCover w w'
    fun i => h i

theorem glue_away {S : Type} [CommRing S] {X : Scheme.{0}} {ι : Type} (f : ι → S)
    (hf : Ideal.span (Set.range f) = ⊤) (z : ∀ i, Sp (Localization.Away (f i)) ⟶ X)
    (h : ∀ i j (T : Type) [CommRing T] (a : Localization.Away (f i) →+* T) (b : Localization.Away (f j) →+* T),
      a.comp (algebraMap S _) = b.comp (algebraMap S _) → spMap a ≫ z i = spMap b ≫ z j) :
    ∃ w : Sp S ⟶ X, ∀ i, spMap (algebraMap S (Localization.Away (f i))) ≫ w = z i := by
  let U := (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of S) f hf).openCover
  refine ⟨Scheme.Cover.glueMorphisms U (fun i => z i) ?_, fun i => Scheme.Cover.ι_glueMorphisms U (fun i => z i) _ i⟩
  intro i j
  show pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (f i)))))
      (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (f j))))) ≫ z i =
    pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (f i)))))
      (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (f j))))) ≫ z j
  rw [← cancel_epi (pullbackSpecIso S (Localization.Away (f i)) (Localization.Away (f j))).inv,
    pullbackSpecIso_inv_fst_assoc, pullbackSpecIso_inv_snd_assoc]
  exact h i j _ _ _ Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap

end GlobalTheory.FlagMod.FieldFlag.Glue

noncomputable section
namespace GlobalTheory.FlagMod.FieldFlag.Glue

open MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem initSpan_comp_equiv {R N N' : Type} [CommRing R] [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']
    {m : ℕ} (V : N ≃ₗ[R] N') (w : Fin m → N) (j : ℕ) :
    initSpan R (fun a => V (w a)) j = (initSpan R w j).map (V : N →ₗ[R] N') := by
  unfold initSpan
  rw [Submodule.map_span, ← Set.image_comp]
  rfl

theorem compat_of_uniq {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {Z : Scheme.{0}} {π : Z ⟶ Y.X}
    (F : Frames Y π) {S : Type} [CommRing S] [Algebra c.F S] (P : FrPt Xo c S)
    (huniq : ∀ (S' : Type) [CommRing S'] [Algebra c.F S'] (P₁ : FrPt Xo c S') (z₁ z₂ : Sp S' ⟶ Z),
      F.Lies z₁ P₁ → F.Lies z₂ P₁ → z₁ = z₂) (f g : S)
    (Pf : FrPt Xo c (Localization.Away f)) (hPf : FrMap (IsScalarTower.toAlgHom c.F S (Localization.Away f)) P Pf)
    (Pg : FrPt Xo c (Localization.Away g)) (hPg : FrMap (IsScalarTower.toAlgHom c.F S (Localization.Away g)) P Pg)
    (zf : Sp (Localization.Away f) ⟶ Z) (zg : Sp (Localization.Away g) ⟶ Z) (hf : F.Lies zf Pf) (hg : F.Lies zg Pg)
    (T : Type) [CommRing T] (a : Localization.Away f →+* T) (b : Localization.Away g →+* T)
    (hab : a.comp (algebraMap S _) = b.comp (algebraMap S _)) : spMap a ≫ zf = spMap b ≫ zg := by
  letI : Algebra c.F T := ((a.comp (algebraMap S _)).comp (algebraMap c.F S)).toAlgebra
  have hca : ∀ r : c.F, a (algebraMap c.F (Localization.Away f) r) = algebraMap c.F T r := fun r => by
    rw [IsScalarTower.algebraMap_apply c.F S (Localization.Away f)]
    rfl
  have hcb : ∀ r : c.F, b (algebraMap c.F (Localization.Away g) r) = algebraMap c.F T r := fun r => by
    rw [IsScalarTower.algebraMap_apply c.F S (Localization.Away g)]
    exact (RingHom.congr_fun hab (algebraMap c.F S r)).symm
  let a' : Localization.Away f →ₐ[c.F] T := AlgHom.mk a hca
  let b' : Localization.Away g →ₐ[c.F] T := AlgHom.mk b hcb
  have ha : a'.toRingHom = a := rfl
  have hb : b'.toRingHom = b := rfl
  obtain ⟨Q, hQ⟩ := exists_frMap a' Pf
  have h1 : FrMap (a'.comp (IsScalarTower.toAlgHom c.F S (Localization.Away f))) P Q :=
    GlobalTheory.FlagTan.frMap_comp hPf hQ (fun _ => rfl)
  have h2 : FrMap b' Pg Q :=
    GlobalTheory.FlagTan.frMap_of_comp hPg h1 (fun s => (RingHom.congr_fun hab s).symm)
  have e := huniq T Q _ _ (hf.frMap hQ) (hg.frMap h2)
  rw [ha, hb] at e
  exact e

theorem lies_of_local {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {Z : Scheme.{0}} {π : Z ⟶ Y.X}
    (F : Frames Y π) {S : Type} [CommRing S] [Algebra c.F S] (P : FrPt Xo c S)
    (huniq : ∀ (S' : Type) [CommRing S'] [Algebra c.F S'] (P₁ : FrPt Xo c S') (z₁ z₂ : Sp S' ⟶ Z),
      F.Lies z₁ P₁ → F.Lies z₂ P₁ → z₁ = z₂)
    (hloc : ∀ q : PrimeSpectrum S, ∃ f : S, f ∉ q.asIdeal ∧ ∃ z : Sp (Localization.Away f) ⟶ Z,
      ∀ P' : FrPt Xo c (Localization.Away f), FrMap (IsScalarTower.toAlgHom c.F S (Localization.Away f)) P P' →
        F.Lies z P') :
    ∃ z : Sp S ⟶ Z, F.Lies z P := by
  choose f hfq z hz using hloc
  have hspan : Ideal.span (Set.range f) = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    exact hfq ⟨M, hM.isPrime⟩ (hle (Ideal.subset_span ⟨_, rfl⟩))
  have hP : ∀ q, ∃ Pq : FrPt Xo c (Localization.Away (f q)),
      FrMap (IsScalarTower.toAlgHom c.F S (Localization.Away (f q))) P Pq := fun q => exists_frMap _ P
  choose Pq hPq using hP
  obtain ⟨w, hw⟩ := glue_away f hspan z (fun i j T _ a b hab =>
    compat_of_uniq F P huniq (f i) (f j) (Pq i) (hPq i) (Pq j) (hPq j) (z i) (z j)
      (hz i _ (hPq i)) (hz j _ (hPq j)) T a b hab)
  refine ⟨w, ?_⟩
  unfold Frames.Lies
  refine ⟨?_, ?_⟩
  · apply ext_away f hspan
    intro q
    have hLq := hz q _ (hPq q)
    unfold Frames.Lies at hLq
    rw [← Category.assoc, hw q, hLq.1, ← frX_frMap (hPq q), Category.assoc]
    rfl
  · intro S' _ _ ψ P' hP' k z' hz'w hzk hx σ i
    subst hz'w
    have hM := F.inM hzk hx
    have e1 := fun (w' : Fin (Dw.mult σ) → ReciprocityTheory.ChartRestriction.G.PullbackSections.TanM (frX P' ≫ Y.j) Y.t.G) =>
      initSpan_comp_equiv (vec (F.M k).toMChart _ hM) (fun a => (vec (F.M k).toMChart _ hM).symm (w' a)) i
    simp only [LinearEquiv.apply_symm_apply] at e1
    rw [e1 (frVec Y P' rfl σ), e1 (F.vecAt k _ hzk hx σ)]
    congr 1
    have hspan' : Ideal.span (Set.range fun q => ψ (f q)) = ⊤ := by
      have h2 : Ideal.map ψ (Ideal.span (Set.range f)) = ⊤ := by rw [hspan, Ideal.map_top]
      rw [Ideal.map_span, ← Set.range_comp] at h2
      exact h2
    apply initSpan_eq_of_away (fun q => ψ (f q)) hspan'
    intro q
    try dsimp only
    obtain ⟨P'', hP''⟩ := exists_frMap (IsScalarTower.toAlgHom c.F S' (Localization.Away (ψ (f q)))) P'
    have hmap : ∀ s : S, Localization.awayMapₐ ψ (f q) (algebraMap S (Localization.Away (f q)) s) =
        algebraMap S' (Localization.Away (ψ (f q))) (ψ s) := fun s => by
      first
        | exact IsLocalization.map_eq _ _
        | simp [IsLocalization.Away.mapₐ, IsLocalization.Away.map, IsLocalization.map_eq]
    have e3 : (Localization.awayMapₐ ψ (f q)).comp (IsScalarTower.toAlgHom c.F S (Localization.Away (f q))) =
        (IsScalarTower.toAlgHom c.F S' (Localization.Away (ψ (f q)))).comp ψ := AlgHom.ext fun s => hmap s
    have hPP'' : FrMap ((IsScalarTower.toAlgHom c.F S' (Localization.Away (ψ (f q)))).comp ψ) P P'' :=
      GlobalTheory.FlagTan.frMap_comp hP' hP'' (fun _ => rfl)
    have hqP'' : FrMap (Localization.awayMapₐ ψ (f q)) (Pq q) P'' :=
      GlobalTheory.FlagTan.frMap_of_comp (hPq q) hPP'' (fun s => hmap s)
    have ez : spMap (Localization.awayMapₐ ψ (f q)).toRingHom ≫ z q =
        spMap (IsScalarTower.toAlgHom c.F S' (Localization.Away (ψ (f q)))).toRingHom ≫
          spMap ψ.toRingHom ≫ w := by
      calc spMap (Localization.awayMapₐ ψ (f q)).toRingHom ≫ z q
            = spMap (Localization.awayMapₐ ψ (f q)).toRingHom ≫
                spMap (IsScalarTower.toAlgHom c.F S (Localization.Away (f q))).toRingHom ≫ w := by
              rw [← hw q]
              rfl
          _ = spMap ((Localization.awayMapₐ ψ (f q)).comp
                (IsScalarTower.toAlgHom c.F S (Localization.Away (f q)))).toRingHom ≫ w :=
              (spMap_algComp _ _ w).symm
          _ = spMap ((IsScalarTower.toAlgHom c.F S' (Localization.Away (ψ (f q)))).comp ψ).toRingHom ≫ w := by
              rw [e3]
          _ = _ := spMap_algComp _ _ w
    have hzk'' : ⊤ ≤ (spMap (IsScalarTower.toAlgHom c.F S' (Localization.Away (ψ (f q)))).toRingHom ≫
        spMap ψ.toRingHom ≫ w) ⁻¹ᵁ F.U k := le_preimage_comp _ hzk
    have hx'' : (spMap (IsScalarTower.toAlgHom c.F S' (Localization.Away (ψ (f q)))).toRingHom ≫
        spMap ψ.toRingHom ≫ w) ≫ π = frX P'' ≫ Y.j := by
      rw [Category.assoc, hx, ← Category.assoc, frX_frMap hP'']
    have hLq := hz q _ (hPq q)
    unfold Frames.Lies at hLq
    have LA := hLq.2 (Localization.Away (ψ (f q))) (Localization.awayMapₐ ψ (f q)) P'' hqP'' k _ ez hzk'' hx'' σ i
    have hM'' := F.inM hzk'' hx''
    have et : spMap (IsScalarTower.toAlgHom c.F S' (Localization.Away (ψ (f q)))).toRingHom ≫ (frX P' ≫ Y.j) =
        frX P'' ≫ Y.j := by
      rw [← Category.assoc, frX_frMap hP'']
    have cA : ∀ a, (vec (F.M k).toMChart _ hM'').symm (frVec Y P'' rfl σ a) =
        fun t => algebraMap S' (Localization.Away (ψ (f q))) ((vec (F.M k).toMChart _ hM).symm (frVec Y P' rfl σ a) t) := by
      intro a
      rw [LinearEquiv.symm_apply_eq, ← tanPull_frVec hP'' rfl rfl et σ a]
      conv_lhs => rw [← LinearEquiv.apply_symm_apply (vec (F.M k).toMChart _ hM) (frVec Y P' rfl σ a)]
      exact tanPull_vec _ _ _ _ _ _
    have cB : ∀ a, (vec (F.M k).toMChart _ hM'').symm (F.vecAt k _ hzk'' hx'' σ a) =
        fun t => algebraMap S' (Localization.Away (ψ (f q))) ((vec (F.M k).toMChart _ hM).symm (F.vecAt k _ hzk hx σ a) t) := by
      intro a
      unfold Frames.vecAt
      simp only [LinearEquiv.symm_apply_apply]
      funext t
      unfold Frames.uAt
      try simp only [Matrix.map_apply]
      rw [ev_spMap _ (spMap ψ.toRingHom ≫ w) (F.U k) hzk]
      rfl
    have L2 : initSpan (Localization.Away (ψ (f q))) (fun a => (vec (F.M k).toMChart _ hM'').symm (frVec Y P'' rfl σ a)) i =
        initSpan (Localization.Away (ψ (f q))) (fun a => (vec (F.M k).toMChart _ hM'').symm (F.vecAt k _ hzk'' hx'' σ a)) i := by
      rw [initSpan_comp_equiv (vec (F.M k).toMChart _ hM'').symm (frVec Y P'' rfl σ),
        initSpan_comp_equiv (vec (F.M k).toMChart _ hM'').symm (F.vecAt k _ hzk'' hx'' σ), LA]
    simpa only [cA, cB] using L2
end GlobalTheory.FlagMod.FieldFlag.Glue

namespace GlobalTheory.FlagMod.FieldFlag

theorem exists_lies_of_local : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (A : Atlas Y p) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1)) (κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)) [∀ b w, IsOpenImmersion (κ b w)] (hZ : Cells A π g κ) (ht : FlagCellFrameChangeTriangular hZ) (S : Type) [CommRing S] [Algebra c.F S] (P : FrPt Xo c S), (∀ (S' : Type) [CommRing S'] [Algebra c.F S'] (P₁ : FrPt Xo c S') (z₁ z₂ : Sp S' ⟶ Z), (cellFrames hZ ht).Lies z₁ P₁ → (cellFrames hZ ht).Lies z₂ P₁ → z₁ = z₂) → (∀ q : PrimeSpectrum S, ∃ f : S, f ∉ q.asIdeal ∧ ∃ z : Sp (Localization.Away f) ⟶ Z, ∀ P' : FrPt Xo c (Localization.Away f), FrMap (IsScalarTower.toAlgHom c.F S (Localization.Away f)) P P' → (cellFrames hZ ht).Lies z P') → ∃ z : Sp S ⟶ Z, (cellFrames hZ ht).Lies z P := by
  intro E _ _ _ H Dw l Xo c Y p A Z π g κ _ hZ ht S _ _ P huniq hloc
  exact Glue.lies_of_local (cellFrames hZ ht) P huniq hloc

end GlobalTheory.FlagMod.FieldFlag
