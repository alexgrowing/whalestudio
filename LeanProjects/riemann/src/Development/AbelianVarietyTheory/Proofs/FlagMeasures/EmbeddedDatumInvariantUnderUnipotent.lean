import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AdaptSelf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormGeometrySummary
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagFramesSameGradedDefinitePartLatticeEq

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt GlobalTheory.DegAsm
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.DegAsm.DatMove
open AdaptInv

theorem sup_iff {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (t : M ≃+ M)
    {A B A' B' : Submodule R M} (h : ∀ y, t y ∈ A ↔ y ∈ B) (h' : ∀ y, t y ∈ A' ↔ y ∈ B') (y : M) :
    t y ∈ A ⊔ A' ↔ y ∈ B ⊔ B' := by
  simp only [Submodule.mem_sup]
  constructor
  · rintro ⟨a, ha, b, hb, hab⟩
    refine ⟨t.symm a, (h _).1 (by simpa using ha), t.symm b, (h' _).1 (by simpa using hb), ?_⟩
    apply t.injective
    simp [hab]
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨t a, (h _).2 ha, t b, (h' _).2 hb, by simp⟩

theorem sup_iff_of_sub {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (t : M ≃+ M)
    {A B C : Submodule R M} (h : ∀ y, t y ∈ A ↔ y ∈ B) (h' : ∀ y, t y ∈ C ↔ y ∈ C) {y : M}
    (hy : t y - y ∈ C) : y ∈ A ⊔ C ↔ y ∈ B ⊔ C := by
  rw [← sup_iff t h h' y]
  have h1 : t y - y ∈ A ⊔ C := Submodule.mem_sup_right hy
  rw [← Submodule.add_mem_iff_right _ h1]
  simp

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V] {H : HermSpace K V} {r : ℕ}

def push (s : V ≃ₗ[K] V) (hs : ∀ x y, H.B (s x) (s y) = H.B x y) (F : FlagD H r) : FlagD H r where
  e a := s (F.e a)
  T := F.T
  indep := F.indep.map' (s : V →ₗ[K] V) s.ker
  iso a b := by rw [hs]; exact F.iso a b
  zperp a := by rw [hs]; exact F.zperp a
  zz := by rw [hs]; exact F.zz
  hT := F.hT

variable (s : V ≃ₗ[K] V) (hs : ∀ x y, H.B (s x) (s y) = H.B x y)

theorem push_X (F : FlagD H r) : (push s hs F).X = F.X.map (s : V →ₗ[K] V) := by
  unfold FlagD.X FlagD.Xa
  rw [Submodule.map_span, Set.image_image]
  rfl

theorem hermFrameMapIsometry_frameSpan (F G : FlagD H r) : V0 (push s hs F) (push s hs G) = (V0 F G).map (s : V →ₗ[K] V) := by
  unfold V0
  rw [push_X, push_X, Submodule.map_sup, Submodule.map_sup, Submodule.map_span, Set.image_pair]
  rfl

theorem mem_map_iff (S : Submodule K V) (y : V) : s y ∈ S.map (s : V →ₗ[K] V) ↔ y ∈ S := by
  constructor
  · rintro ⟨x, hx, h⟩
    exact s.injective h ▸ hx
  · exact fun h => ⟨y, h, rfl⟩

include hs in
theorem perp_map_iff (S : Submodule K V) (y : V) : s y ∈ perp H (S.map (s : V →ₗ[K] V)) ↔ y ∈ perp H S := by
  simp only [mem_perp_iff]
  constructor
  · intro h x hx
    rw [← hs]; exact h _ ⟨x, hx, rfl⟩
  · rintro h _ ⟨x, hx, rfl⟩
    exact (hs _ _).trans (h x hx)

theorem push_X_iff (F : FlagD H r) (y : V) : s y ∈ (push s hs F).X ↔ y ∈ F.X := by
  rw [push_X, mem_map_iff]

variable {R : Type} [CommRing R] [Algebra R K] [Module R V] [IsScalarTower R K V]

theorem hermIsometry_mem_flagPairDefinitePartLattice_iff (F G : FlagD H r) {Λ Λ' : Submodule R V} (h : ∀ y, s y ∈ Λ' ↔ y ∈ Λ) (y : V) :
    s y ∈ flagPairDefinitePartLattice (push s hs F) (push s hs G) Λ' ↔ y ∈ flagPairDefinitePartLattice F G Λ := by
  have h1 := sup_iff s.toAddEquiv (A' := rs R (push s hs F).X) (B' := rs R F.X) h (push_X_iff s hs F) y
  simp only [flagPairDefinitePartLattice, latL, uPerp, wSp, Submodule.mem_inf, Submodule.restrictScalars_mem]
  rw [hermFrameMapIsometry_frameSpan, perp_map_iff s hs]
  refine and_congr (and_congr ?_ h1) Iff.rfl
  rw [push_X, push_X, ← Submodule.map_sup, perp_map_iff s hs]

theorem smulLat_iff {Λ Λ' : Submodule R V} (h : ∀ y, s y ∈ Λ' ↔ y ∈ Λ) (g : R) (y : V) :
    s y ∈ smulLat g Λ' ↔ y ∈ smulLat g Λ := by
  have hg : ∀ x, s (g • x) = g • s x := fun x => (s : V →ₗ[K] V).map_smul_of_tower g x
  constructor
  · rintro ⟨x, hx, h1⟩
    refine ⟨s.symm x, (h _).1 (by simpa using hx), s.injective ?_⟩
    rw [← h1]
    simpa using hg (s.symm x)
  · rintro ⟨x, hx, rfl⟩
    exact ⟨s x, (h _).2 hx, (hg x).symm⟩

theorem push_graph (F G : FlagD H r) {Λ Λ' : Submodule R V} (h : ∀ y, s y ∈ Λ' ↔ y ∈ Λ) (g : R) (y : V × V) :
    (s.toAddEquiv.prodCongr s.toAddEquiv) y ∈ iotaGraph (push s hs F) (push s hs G) Λ' g ↔
      y ∈ iotaGraph F G Λ g := by
  simp only [iotaGraph, Submodule.mem_inf]
  refine and_congr (and_congr (hermIsometry_mem_flagPairDefinitePartLattice_iff s hs G F h y.1) (hermIsometry_mem_flagPairDefinitePartLattice_iff s hs F G h y.2)) ?_
  refine sup_iff _ (fun p => ?_) (fun p => and_congr (push_X_iff s hs G p.1) (push_X_iff s hs F p.2)) y
  refine and_congr (and_congr (h p.1) (h p.2)) ?_
  have := sup_iff s.toAddEquiv (A' := Λ' ⊓ rs R (push s hs F).X) (B' := Λ ⊓ rs R F.X) (smulLat_iff s h g)
    (fun y => and_congr (h y) (push_X_iff s hs F y)) (p.2 - p.1)
  rw [map_sub] at this
  exact this

theorem sameGr_push (F : FlagD H r) (hN : F.InN (s : V →ₗ[K] V)) : SameGr F (push s hN.1 F) := by
  intro a
  induction a using Fin.lastCases with
  | last => exact hN.2.2.2 _ F.zperp
  | cast a => exact hN.2.2.1 a

theorem flag_vector_mem_base_lattice (F G : FlagD H r) (a : Fin (r + 1)) : F.e a ∈ V0 F G := by
  induction a using Fin.lastCases with
  | last => exact Submodule.mem_sup_right (Submodule.subset_span (Or.inl rfl))
  | cast a => exact Submodule.mem_sup_left (Submodule.mem_sup_left (e_mem_xa F a a.2))

theorem jointSpan_comm (F G : FlagD H r) : V0 F G = V0 G F := by
  unfold V0
  rw [sup_comm F.X, Set.pair_comm]

theorem herm_zero {x y : V} (h : H.B x y = 0) : H.B y x = 0 := by
  rw [← H.herm, h, star_zero]

theorem commonIsotropic_le_flagPairDefinitePartLattice {F G : FlagD H r} (hI : ∀ x ∈ II F G, ∀ w ∈ V0 F G, H.B w x = 0) (Λ : Submodule R V)
    {x : V} (hx : x ∈ II F G) : x ∈ flagPairDefinitePartLattice F G Λ := by
  refine ⟨⟨?_, Submodule.mem_sup_right hx.1⟩, ?_⟩
  · exact (mem_perp_iff _ _ _).2 fun w hw => herm_zero (hI x hx w (Submodule.mem_sup_left hw))
  · exact (mem_perp_iff _ _ _).2 fun w hw => herm_zero (hI x hx w hw)

end GlobalTheory.DegAsm.DatMove

namespace GlobalTheory.DegAsm
open AdaptInv DatMove

theorem datOf_move : ∀ (K V W : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W] [FiniteDimensional K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (H : HermSpace K V) (HW : HermSpace K W) (e : W →ₗ[K] V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ), ∀ (F G G' : FlagD H r) (𝔡 : Ideal (𝓞 K)) (N : NF H r) (g : ℕ), IsEmb F HW e → Adapt F G 𝔡 N → (∀ (s : V ≃ₗ[K] V) (Λ : Submodule (𝓞 K) V), F.InN (s : V →ₗ[K] V) → (∀ a, s (G.e a) - G'.e a ∈ G'.Xa a.val) → datOf F G' e g (s • Λ) = datOf F G e g Λ ∧ lat0 F e (s • Λ) = lat0 F e Λ ∧ latL F G (s • Λ) = latL F G Λ) ∧ ∀ Λ Λ' : Submodule (𝓞 K) V, datOf F G e g Λ = datOf F G e g Λ' → flagPairDefinitePartLattice G F Λ = flagPairDefinitePartLattice G F Λ' ∧ iotaGraph F G Λ (g : 𝓞 K) = iotaGraph F G Λ' (g : 𝓞 K) := by
  intro K V W _ _ _ _ _ _ _ _ _ _ _ _ _ H HW e hK r F G G' 𝔡 N g hE hA
  refine ⟨fun s Λ hN hG => ?_, ?_⟩
  · have hs : ∀ x y, H.B (s x) (s y) = H.B x y := hN.1
    have hF : SameGr F (push s hs F) := sameGr_push s F hN
    have hG' : SameGr G' (push s hs G) := hG
    have hΛ : ∀ y, s y ∈ s • Λ ↔ y ∈ Λ := fun y => by
      constructor
      · rintro ⟨x, hx, h⟩
        exact s.injective h ▸ hx
      · exact fun h => ⟨y, h, rfl⟩
    have hX : ∀ y, s y ∈ F.X ↔ y ∈ F.X := fun y => by
      have := push_X_iff s hs F y
      rwa [x_eq hF] at this
    have he : ∀ w, s (e w) - e w ∈ F.X := fun w =>
      hN.2.2.2 _ fun a => (hE.2 (e w)).2 (Submodule.mem_sup_left ⟨w, rfl⟩) _
    refine ⟨Prod.ext ?_ ?_, ?_, ?_⟩
    · ext w
      refine sup_iff_of_sub s.toAddEquiv (C := rs (𝓞 K) F.X) (fun y => ?_) hX (he w)
      rw [← flagFramesSameGraded_definitePartLattice_eq hG' hF]
      exact hermIsometry_mem_flagPairDefinitePartLattice_iff s hs G F hΛ y
    · ext w
      refine sup_iff_of_sub (s.toAddEquiv.prodCongr s.toAddEquiv)
        (C := (rs (𝓞 K) F.X).prod (rs (𝓞 K) F.X)) (fun y => ?_)
        (fun p => and_congr (hX p.1) (hX p.2)) ⟨he w.1, he w.2⟩
      rw [← iotaGraph_eq hF hG']
      exact push_graph s hs F G hΛ _ y
    · ext w
      exact sup_iff_of_sub s.toAddEquiv (C := rs (𝓞 K) F.X) hΛ hX (he w)
    · ext y
      refine and_congr_right fun hy => sup_iff_of_sub s.toAddEquiv (C := rs (𝓞 K) F.X) hΛ hX ?_
      exact hN.2.2.2 y fun a => herm_zero
        ((mem_perp_iff _ _ _).1 hy _ (Submodule.mem_sup_left (e_mem_xa F a a.2)))
  · obtain ⟨-, h, h'⟩ := hA
    have h0 := (GlobalTheory.DegCnt.NF.geometry K V H hK r N).1.2.2.2.2.2.1
    have h1 : II N.F N.F' = II F G := by simp only [II, x_eq h, x_eq h']
    rw [h1, x_eq h, sitesCommonSpace_v0_eq_Vp h h'] at h0
    have hI : ∀ x ∈ II F G, ∀ w ∈ V0 F G, H.B w x = 0 := fun x hx => (h0 x hx.1).2 hx
    have hI' : ∀ x ∈ II G F, ∀ w ∈ V0 G F, H.B w x = 0 := fun x hx w hw =>
      hI x ⟨hx.2, hx.1⟩ w (jointSpan_comm G F ▸ hw)
    have hdec : ∀ y ∈ wSp F G, ∃ w, y - e w ∈ F.X := fun y hy => by
      have := (hE.2 y).1 fun a => herm_zero ((mem_perp_iff _ _ _).1 hy _ (flag_vector_mem_base_lattice F G a))
      obtain ⟨_, ⟨w, rfl⟩, x, hx, rfl⟩ := Submodule.mem_sup.1 this
      exact ⟨w, by simpa using hx⟩
    have hker : ∀ y ∈ wSp F G, ∀ y' ∈ wSp F G, y - y' ∈ F.X → y - y' ∈ II F G := fun y hy y' hy' hx =>
      (h0 _ hx).1 fun w hw => herm_zero ((mem_perp_iff _ _ _).1 (Submodule.sub_mem _ hy hy') w hw)
    have hw : wSp G F = wSp F G := by rw [wSp, jointSpan_comm]; rfl
    have hL : ∀ Λ : Submodule (𝓞 K) V, ∀ y ∈ flagPairDefinitePartLattice G F Λ, y ∈ wSp F G := fun Λ y hy => hw ▸ hy.2
    have key : ∀ Λ Λ' : Submodule (𝓞 K) V, datOf F G e g Λ = datOf F G e g Λ' →
        flagPairDefinitePartLattice G F Λ ≤ flagPairDefinitePartLattice G F Λ' ∧ iotaGraph F G Λ (g : 𝓞 K) ≤ iotaGraph F G Λ' (g : 𝓞 K) := by
      intro Λ Λ' hd
      refine ⟨fun y hy => ?_, fun y hy => ?_⟩
      · obtain ⟨w, hx⟩ := hdec y (hL _ y hy)
        have a1 : w ∈ (datOf F G e g Λ).1 := by
          have := Submodule.sub_mem (flagPairDefinitePartLattice G F Λ ⊔ rs (𝓞 K) F.X) (Submodule.mem_sup_left hy)
            (Submodule.mem_sup_right hx)
          rw [sub_sub_cancel] at this
          exact this
        rw [hd] at a1
        obtain ⟨m, hm, x, hx', hmx⟩ := Submodule.mem_sup.1 a1
        have hmx : m + x = e w := hmx
        have a2 : y - m ∈ F.X := by
          have := F.X.add_mem hx hx'
          convert this using 1
          rw [← hmx]; abel
        have a3 := hker y (hL _ y hy) m (hL _ m hm) a2
        have := Submodule.add_mem _ (commonIsotropic_le_flagPairDefinitePartLattice hI' Λ' ⟨a3.2, a3.1⟩) hm
        simpa using this
      · obtain ⟨w, hx⟩ := hdec y.1 (hL _ _ hy.1.1)
        obtain ⟨w', hx'⟩ := hdec y.2 hy.1.2.2
        have a1 : (w, w') ∈ (datOf F G e g Λ).2 := by
          have := Submodule.sub_mem (iotaGraph F G Λ (g : 𝓞 K) ⊔ (rs (𝓞 K) F.X).prod (rs (𝓞 K) F.X))
            (Submodule.mem_sup_left hy) (Submodule.mem_sup_right (x := y - (e w, e w')) ⟨hx, hx'⟩)
          rw [sub_sub_cancel] at this
          exact this
        rw [hd] at a1
        obtain ⟨m, hm, x, hx2, hmx⟩ := Submodule.mem_sup.1 a1
        have hmx1 : m.1 + x.1 = e w := congrArg Prod.fst hmx
        have hmx2 : m.2 + x.2 = e w' := congrArg Prod.snd hmx
        have a2 : y.1 - m.1 ∈ F.X := by
          have := F.X.add_mem hx hx2.1
          convert this using 1
          rw [← hmx1]; abel
        have a2' : y.2 - m.2 ∈ F.X := by
          have := F.X.add_mem hx' hx2.2
          convert this using 1
          rw [← hmx2]; abel
        have a3 := hker _ (hL _ _ hy.1.1) _ (hL _ _ hm.1.1) a2
        have a3' := hker _ hy.1.2.2 _ hm.1.2.2 a2'
        have a4 : y - m ∈ iotaGraph F G Λ' (g : 𝓞 K) :=
          ⟨⟨commonIsotropic_le_flagPairDefinitePartLattice hI' Λ' ⟨a3.2, a3.1⟩, commonIsotropic_le_flagPairDefinitePartLattice hI Λ' a3'⟩, Submodule.mem_sup_right ⟨a3.2, a3'.1⟩⟩
        have := Submodule.add_mem _ a4 hm
        simpa using this
    exact fun Λ Λ' hd => ⟨le_antisymm (key _ _ hd).1 (key _ _ hd.symm).1, le_antisymm (key _ _ hd).2 (key _ _ hd.symm).2⟩

end GlobalTheory.DegAsm
