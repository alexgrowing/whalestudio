import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Formalism.SharpRestriction.CuspSpanNormBounds.NonGenericAndKTwoTheorems
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.FrameCoefficientData
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GgNone
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsPrincipalIdealRingOfHenselian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEqZpowMulUnit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemPerpSpan
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NotField
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SpanToZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairCoordinatesTransportUnitaryMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramePairCoordinatesTransportInnerLattices
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramePairCoordinatesTransportInnerData

noncomputable section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IndefiniteRowSideFullHecke.FrameCoefficientData
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.NonGenericCompare

section Place
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [StarRing E]
variable (o : Type) [CommRing o] [Algebra o F] [Algebra o E]

structure SamePlace (L : LocE F E) : Prop where
  int_iff : ∀ x : F, x ∈ 𝒪[F] ↔ ∃ a : o, algebraMap o F a = x
  star_eq : ∀ x : E, star x = L.cj x

variable {o}

theorem SamePlace.mem_O [IsScalarTower o F E] {L : LocE F E} (h : SamePlace o L) (x : E) :
    x ∈ MaxOrd o E ↔ x ∈ L.O := by
  rw [L.O_def, mem_integralClosure_iff]
  letI : Algebra o 𝒪[F] :=
    ((algebraMap o F).codRestrict 𝒪[F] fun a => (h.int_iff _).2 ⟨a, rfl⟩).toAlgebra
  haveI : IsScalarTower o 𝒪[F] E := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply o F E]; rfl
  haveI : Algebra.IsIntegral o 𝒪[F] := ⟨fun y => by
    obtain ⟨a, ha⟩ := (h.int_iff y).1 y.2
    have : y = algebraMap o 𝒪[F] a := Subtype.ext ha.symm
    rw [this]; exact isIntegral_algebraMap⟩
  exact ⟨fun hx => hx.tower_top, fun hx => isIntegral_trans x hx⟩

end Place

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] [StarRing E]
variable {o : Type} [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] [Algebra o F]
  [IsFractionRing o F] [Algebra o E] [IsScalarTower o F E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {H : HermSp M V} {r k : ℕ}

structure Match (P : LocNG.FPair H r) (D : Data o F E V r) : Prop where
  place : SamePlace o M.L
  h_eq : ∀ x y, D.h x y = H.h x y
  ψ_eq : ∀ x, (D.ψ x : ℂ) = M.L.psi0 x
  θ_eq : D.θ = LocNG.theta M
  f_eq : D.A.f = P.A.f
  f'_eq : D.B.f = P.B.f
  y_eq : D.A.y = P.A.es
  y'_eq : D.B.y = P.B.es
  T_eq : D.A.T = P.A.T
  T'_eq : D.B.T = P.B.T

namespace Match
variable {P : LocNG.FPair H r} {D : Data o F E V r} {S : Frames M.L r k}
variable (m : Match P D) (c : Coord P S)

def lat (Λ : Submodule (MaxOrd o E) V) : Submodule M.L.O S.V where
  carrier := {y | c.e.symm y ∈ Λ}
  add_mem' := fun {a b} ha hb => by
    simpa only [Set.mem_setOf_eq, map_add] using Λ.add_mem ha hb
  zero_mem' := by simp
  smul_mem' := fun s a ha => by
    have := Λ.smul_mem ⟨s, (m.place.mem_O _).2 s.2⟩ ha
    change c.e.symm ((s : E) • a) ∈ Λ
    rw [map_smul]; exact this

def unlat (Λ : Submodule M.L.O S.V) : Submodule (MaxOrd o E) V where
  carrier := {y | c.e y ∈ Λ}
  add_mem' := fun {a b} ha hb => by
    simpa only [Set.mem_setOf_eq, map_add] using Λ.add_mem ha hb
  zero_mem' := by simp
  smul_mem' := fun s a ha => by
    have := Λ.smul_mem ⟨s, (m.place.mem_O _).1 s.2⟩ ha
    change c.e ((s : E) • a) ∈ Λ
    rw [map_smul]; exact this

theorem mem_lat (Λ : Submodule (MaxOrd o E) V) (v : V) : c.e v ∈ m.lat c Λ ↔ v ∈ Λ := by
  change c.e.symm (c.e v) ∈ Λ ↔ _
  rw [c.e.symm_apply_apply]

theorem mem_unlat (Λ : Submodule M.L.O S.V) (v : V) : v ∈ m.unlat c Λ ↔ c.e v ∈ Λ := Iff.rfl

theorem lat_unlat (Λ : Submodule M.L.O S.V) : m.lat c (m.unlat c Λ) = Λ := by
  ext y
  obtain ⟨v, rfl⟩ := c.e.surjective y
  rw [mem_lat, mem_unlat]

theorem unlat_lat (Λ : Submodule (MaxOrd o E) V) : m.unlat c (m.lat c Λ) = Λ := by
  ext y
  rw [mem_unlat, mem_lat]

theorem lat_inj {Λ Λ' : Submodule (MaxOrd o E) V} : m.lat c Λ = m.lat c Λ' ↔ Λ = Λ' :=
  ⟨fun h => by rw [← m.unlat_lat c Λ, h, unlat_lat], fun h => by rw [h]⟩

theorem lat_le {Λ Λ' : Submodule (MaxOrd o E) V} : m.lat c Λ ≤ m.lat c Λ' ↔ Λ ≤ Λ' :=
  ⟨fun h v hv => (m.mem_lat c _ _).1 (h ((m.mem_lat c _ _).2 hv)), fun h _ hv => h hv⟩

theorem lat_span (s : Set V) :
    m.lat c (Submodule.span (MaxOrd o E) s) = Submodule.span M.L.O (c.e '' s) := by
  apply le_antisymm
  · rw [← m.lat_unlat c (Submodule.span M.L.O _), lat_le, Submodule.span_le]
    exact fun v hv => Submodule.subset_span ⟨v, hv, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    exact (m.mem_lat c _ _).2 (Submodule.subset_span hv)

def dat (d : D.InnerDatum) : S.Datum :=
  (m.lat c d.L, m.lat c d.L', {p | (c.e.symm p.1, c.e.symm p.2) ∈ d.Γ})

theorem mem_dat (d : D.InnerDatum) (v w : V) : (c.e v, c.e w) ∈ (m.dat c d).2.2 ↔ (v, w) ∈ d.Γ := by
  simp [dat]

theorem grp_e (g : V ≃ₗ[E] V) (v : V) : c.grp g (c.e v) = c.e (g v) := CoordUnip.grp_apply c g v

include m

theorem hS (x y : V) : S.h (c.e x) (c.e y) = D.h x y := by rw [c.h_eq, m.h_eq]

theorem fS (a : Fin (r + 1)) : S.f a = c.e (D.A.f a) := by rw [c.f_eq, m.f_eq]
theorem fS' (a : Fin (r + 1)) : S.f' a = c.e (D.B.f a) := by rw [c.f'_eq, m.f'_eq]
theorem yS (a : Fin r) : S.es a = c.e (D.A.y a) := by rw [c.es_eq, m.y_eq]
theorem yS' (a : Fin r) : S.es' a = c.e (D.B.y a) := by rw [c.es'_eq, m.y'_eq]

include c in
theorem θS : D.θ = S.th := by rw [m.θ_eq, CoordUnip.theta_eq c]

theorem carries_iff (g : V ≃ₗ[E] V) (A B : Submodule (MaxOrd o E) V) :
    Carries g (A : Set V) (B : Set V) ↔ m.lat c B = c.grp g • m.lat c A := by
  have key : ∀ v, c.e (g v) ∈ c.grp g • m.lat c A ↔ v ∈ A := fun v => by
    rw [TermBasic.mem_smul, ← grp_e c, ← m.mem_lat c]
    simp
  constructor
  · intro h
    ext y
    obtain ⟨v, rfl⟩ := c.e.surjective y
    obtain ⟨v, rfl⟩ := g.surjective v
    rw [key, mem_lat]; exact h v
  · intro h v
    rw [SetLike.mem_coe, SetLike.mem_coe, ← key, ← h, mem_lat]

theorem mem_stab (g : V ≃ₗ[E] V) (A : Submodule (MaxOrd o E) V) :
    g ∈ stab E A.toAddSubgroup ↔ c.grp g ∈ MulAction.stabilizer S.GLV (m.lat c A) := by
  rw [MulAction.mem_stabilizer_iff, eq_comm, ← carries_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, fun _ hv => hv.elim⟩⟩

omit m in
theorem mem_spanTo (A : Frame F V r) (g : Fin (r + 1) → S.V) (hg : ∀ a, g a = c.e (A.f a)) (j : ℕ) (v : V) :
    v ∈ A.X E j ↔ c.e v ∈ S.spanTo g j := by
  have : S.spanTo g j = (A.X E j).map (c.e : V →ₗ[E] S.V) := by
    rw [Frame.X, Submodule.map_span, Set.image_image]
    unfold Frames.spanTo
    congr 2
    exact funext hg
  rw [this]
  exact ⟨fun h => ⟨v, h, rfl⟩, fun ⟨y, hy, e⟩ => c.e.injective e ▸ hy⟩

theorem mem_perp (A : Submodule E V) (B : Submodule E S.V) (h : ∀ v, v ∈ A ↔ c.e v ∈ B) (v : V) :
    v ∈ IndefiniteRowSideFullHecke.FrameCoefficientData.perp D.h (A : Set V) ↔ c.e v ∈ HL.perp M.L S.Hm B := by
  constructor
  · intro hv y hy
    obtain ⟨w, rfl⟩ := c.e.surjective y
    exact (m.hS c v w).trans (hv w ((h w).2 hy))
  · intro hv w hw
    exact (m.hS c v w).symm.trans (hv _ ((h w).1 hw))

theorem mem_isom (g : V ≃ₗ[E] V) : g ∈ isom D.h ↔ c.grp g ∈ isomG M.L S.Hm := by
  constructor
  · intro h x y
    obtain ⟨v, rfl⟩ := c.e.surjective x
    obtain ⟨w, rfl⟩ := c.e.surjective y
    rw [grp_e, grp_e]
    exact (m.hS c _ _).trans ((h v w).trans (m.hS c _ _).symm)
  · intro h v w
    have := h (c.e v) (c.e w)
    rw [grp_e, grp_e] at this
    exact (m.hS c _ _).symm.trans (this.trans (m.hS c _ _))

theorem mem_N (A : Frame F V r) (f : Fin (r + 1) → S.V) (hf : ∀ a, f a = c.e (A.f a)) (g : V ≃ₗ[E] V) :
    g ∈ A.N D.h ↔ c.grp g ∈ S.Nof f := by
  have hX := mem_spanTo c A f hf
  have hP := m.mem_perp c _ _ (hX r)
  simp only [Frame.N, Frames.Nof, Subgroup.mem_inf, Subgroup.mem_iInf, m.mem_isom c]
  have tr : ∀ (s : Set V) (B : Submodule E S.V), (∀ v, v ∈ s ↔ c.e v ∈ B) →
      ((∀ v, g v ∈ s ↔ v ∈ s) ↔ ∀ y, c.grp g y ∈ B ↔ y ∈ B) := fun s B h => by
    rw [c.e.surjective.forall]
    simp only [grp_e, ← h]
  have tr2 : ∀ (s : Set V) (B : Submodule E S.V) (j : ℕ), (∀ v, v ∈ s ↔ c.e v ∈ B) →
      ((∀ v ∈ s, g v - v ∈ A.X E j) ↔ ∀ y ∈ B, c.grp g y - y ∈ S.spanTo f j) := fun s B j h => by
    rw [c.e.surjective.forall]
    simp only [grp_e, ← h, ← map_sub, ← hX]
  have z : ∀ v, g v ∈ A.X E 0 ↔ v ∈ A.X E 0 := fun v => by simp [Frame.X]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨h1, fun j => ⟨(tr _ _ (hX _)).1 ?_, (tr2 _ _ _ (hX _)).1 (h2 j).2⟩⟩,
      (tr _ _ hP).1 fun v => ?_, (tr2 _ _ _ hP).1 h3.2⟩
    · by_cases hj : (j : ℕ) + 1 < r
      · exact (h2 ⟨j + 1, hj⟩).1
      · have : (j : ℕ) + 1 = r := by omega
        rw [this]; exact h3.1
    · have hi := (m.mem_isom c g).2 h1
      constructor
      · intro hv w hw
        rw [← hi]; exact hv _ ((h3.1 w).2 hw)
      · intro hv w hw
        obtain ⟨w, rfl⟩ := g.surjective w
        rw [hi]; exact hv _ ((h3.1 w).1 hw)
  · rintro ⟨⟨h1, h2⟩, h3⟩
    have pr : ∀ j ≤ r, ∀ v, g v ∈ A.X E j ↔ v ∈ A.X E j := fun j hj => by
      rcases j with _ | j
      · exact z
      · exact (tr _ _ (hX _)).2 (h2 ⟨j, hj⟩).1
    exact ⟨⟨h1, fun j => ⟨pr j j.2.le, (tr2 _ _ _ (hX _)).2 (h2 j).2⟩⟩, pr r le_rfl, (tr2 _ _ _ hP).2 h3.2⟩

theorem mem_St (g : V ≃ₗ[E] V) : g ∈ D.St ↔ c.grp g ∈ S.St :=
  and_congr (m.mem_N c _ _ (m.fS c) g) (m.mem_N c _ _ (m.fS' c) g)

theorem mem_StInt (g : V ≃ₗ[E] V) : g ∈ D.StInt ↔ c.grp g ∈ S.K0 := by
  simp only [Data.StInt, Frames.K0, Subgroup.mem_inf, m.mem_St c, m.mem_stab c, lat_span,
    ← Set.range_comp, Function.comp_def, ← m.fS c, ← m.fS' c]

theorem mem_ME (v : V) : v ∈ D.ME ↔ c.e v ∈ S.ME := by
  have : S.ME = D.ME.map (c.e : V →ₗ[E] S.V) := by
    rw [Data.ME, Submodule.map_span, Set.image_union, Submodule.span_union, Frames.ME,
      TermBasic.spanTo_top, TermBasic.spanTo_top]
    simp only [← Set.range_comp, Function.comp_def, LinearEquiv.coe_coe, ← m.fS c, ← m.fS' c]
  rw [this]
  exact ⟨fun h => ⟨v, h, rfl⟩, fun ⟨y, hy, e⟩ => c.e.injective e ▸ hy⟩

theorem mem_riemannRochSpace_iff_regularAt_everywhere (g : V ≃ₗ[E] V) : g ∈ D.H0 ↔ c.grp g ∈ S.H0 := by
  simp only [Data.H0, Frames.H0, Subgroup.mem_inf, m.mem_isom c]
  refine and_congr_right fun _ => ⟨fun h => ?_, fun h => ⟨fun v => by simp, fun v hv => ?_⟩⟩
  · have h2 : ∀ v ∈ D.ME, g v = v := fun v hv => sub_eq_zero.1 (h.2 v hv)
    refine ⟨fun y => ?_, fun y hy => ?_⟩
    · obtain ⟨v, rfl⟩ := c.e.surjective y
      rw [grp_e, ← m.mem_ME c, ← m.mem_ME c]
      refine ⟨fun hv => ?_, fun hv => (h2 v hv).symm ▸ hv⟩
      rwa [g.injective (h2 _ hv)] at hv
    · obtain ⟨v, rfl⟩ := c.e.surjective y
      rw [grp_e, h2 v ((m.mem_ME c v).2 hy), sub_self]; exact zero_mem _
  · have := h.2 _ ((m.mem_ME c v).1 hv)
    rw [grp_e, ← map_sub, Submodule.mem_bot, c.e.map_eq_zero_iff] at this
    exact this

theorem psi_eq (g : V ≃ₗ[E] V) :
    (D.psi g : ℂ) = S.psi (c.grp g) ∧ (D.psi' g : ℂ) = S.psi' (c.grp g) := by
  simp only [Data.psi, Data.psi', m.ψ_eq, Frames.psi, Frames.psi', Frames.psiOf, Frames.coef, Data.θinv,
    Frame.coeffSum, m.θS c, m.fS c, m.fS' c, m.yS c, m.yS' c, grp_e, m.hS c, and_self]

theorem inTh_iff (Λ : Submodule (MaxOrd o E) V) (v : V) :
    D.θinv • v ∈ Λ ↔ S.InTh (m.lat c Λ) (c.e v) := by
  have h0 : S.th ≠ 0 := by
    unfold Frames.th
    split_ifs
    · simpa using S.ϖ_irr.ne_zero
    · exact one_ne_zero
  rw [Data.θinv, m.θS c]
  constructor
  · intro h
    refine ⟨_, (m.mem_lat c _ _).2 h, ?_⟩
    rw [map_smul, smul_smul, ← map_mul, mul_inv_cancel₀ h0, map_one, one_smul]
  · rintro ⟨y, hy, e⟩
    rwa [← m.mem_lat c, map_smul, e, smul_smul, ← map_mul, inv_mul_cancel₀ h0, map_one, one_smul]

end Match

end GlobalTheory.NonGenericCompare
