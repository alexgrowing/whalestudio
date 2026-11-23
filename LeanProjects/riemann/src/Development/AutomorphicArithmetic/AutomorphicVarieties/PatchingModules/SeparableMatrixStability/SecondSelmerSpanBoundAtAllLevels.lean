import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchedSupportCompletions
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ProfDefs

noncomputable section

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools

namespace UpperTheory.V.Pa

variable {l : ℕ} [Fact l.Prime] {L : Loc}

instance (G : Glob l L) : CompactSpace G.G₀ :=
  isCompact_iff_compactSpace.1 (G.η.ker.isClosed_of_isOpen G.η_open).isCompact

namespace Glob.Hom

variable {G G' : Glob l L} (h : G.Hom G')

@[simp] theorem coe_p₀ (g : G.G₀) : (h.p₀ g : G'.Γ) = h.p g := rfl

theorem p₀_cont : Continuous h.p₀ := (h.cont.comp continuous_subtype_val).subtype_mk _

theorem p₀_surj : Function.Surjective h.p₀ := fun g => by
  obtain ⟨a, ha⟩ := h.surj g
  exact ⟨⟨a, by rw [MonoidHom.mem_ker, ← h.η, ha]; exact g.2⟩, Subtype.ext ha⟩

theorem p₀_quot : Topology.IsQuotientMap h.p₀ := h.p₀_cont.isClosedMap.isQuotientMap h.p₀_cont h.p₀_surj

theorem p₀_conj (g : G.G₀) : h.p₀ (G.frame.conj g) = G'.frame.conj (h.p₀ g) :=
  Subtype.ext (by
    change h.p (G.c * g * G.c⁻¹) = G'.c * h.p g * G'.c⁻¹
    rw [map_mul, map_mul, map_inv, h.c])

theorem p₀_φ (v : L.Vl) (g : L.Gv v) : h.p₀ (G.φ v g) = G'.φ v g := Subtype.ext (h.φ v g)

theorem p₀_φu (u : L.St) (g : L.Gu u) : h.p₀ (G.φu u g) = G'.φu u g := Subtype.ext (h.φu u g)

theorem p₀_mem_G' (g : G.G₀) : h.p₀ g ∈ G'.frame.G' ↔ g ∈ G.frame.G' := by
  change G'.ε (h.p g) = 1 ↔ G.ε g = 1
  rw [h.ε]

theorem eps_p₀ (O R : Type) [CommRing O] [Algebra ℤ_[l] O] [CommRing R] [Algebra O R] (g : G.G₀) :
    G'.frame.eps O R (h.p₀ g) = G.frame.eps O R g := by
  change Units.map _ (G'.ε (h.p g)) = Units.map _ (G.ε g)
  rw [h.ε]

theorem locConst_iff {Z : Type} (f : G'.G₀ → Z) : IsLocallyConstant (fun g => f (h.p₀ g)) ↔ IsLocallyConstant f :=
  ⟨fun H s => h.p₀_quot.isOpen_preimage.1 (H s), fun H => H.comp_continuous h.p₀_cont⟩

theorem adicCont_iff {R : Type} [CommRing R] (I : Ideal R) (f : G'.G₀ → R) :
    AdicCont I (fun g => f (h.p₀ g)) ↔ AdicCont I f :=
  forall_congr' fun N => h.locConst_iff fun g => Ideal.Quotient.mk (I ^ N) (f g)

def comp {G'' : Glob l L} (h' : G'.Hom G'') : G.Hom G'' where
  p := h'.p.comp h.p
  cont := h'.cont.comp h.cont
  surj := h'.surj.comp h.surj
  η g := (h'.η _).trans (h.η g)
  c := by rw [MonoidHom.comp_apply, h.c, h'.c]
  ε g := (h'.ε _).trans (h.ε g)
  φ v g := by rw [MonoidHom.comp_apply, h.φ, h'.φ]
  φu u g := by rw [MonoidHom.comp_apply, h.φu, h'.φu]

section Sel

variable {n : ℕ} {A R : Type} [CommRing A] [CommRing R] [Algebra A R] (t : A)
  (ρ : G'.G₀ → Matrix (Fin n) (Fin n) R) (w wi : L.Vl → Matrix (Fin n) (Fin n) R)
  (V : Submodule A (Matrix (Fin n) (Fin n) R)) (z : G'.G₀ → Matrix (Fin n) (Fin n) R)

theorem dY_comp (Y : Matrix (Fin n) (Fin n) R) (g : G.G₀) :
    dY G.frame (fun g => ρ (h.p₀ g)) Y g = dY G'.frame ρ Y (h.p₀ g) := by
  simp only [dY, map_inv]

theorem locAt_iff (v : L.Vl) (Y : Matrix (Fin n) (Fin n) R) :
    LocAt G.frame (fun g => ρ (h.p₀ g)) w wi (fun g => z (h.p₀ g)) v Y ↔ LocAt G'.frame ρ w wi z v Y := by
  refine forall_congr' fun g => ?_
  have e : h.p₀ (G.frame.φ v g) = G'.frame.φ v g := h.p₀_φ v g
  simp only [h.dY_comp, e]
  rfl

theorem sel_iff : (fun g => z (h.p₀ g)) ∈ SelZ G.frame t (fun g => ρ (h.p₀ g)) w wi V ↔ z ∈ SelZ G'.frame t ρ w wi V := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨fun g => ?_, fun i j => (h.adicCont_iff _ fun g => z g i j).1 (h2 i j), fun g g' => ?_, fun g => ?_, ?_,
      fun v => (h6 v).imp fun Y hY => ⟨hY.1, (h.locAt_iff ρ w wi z v Y).1 hY.2⟩⟩
    · obtain ⟨g, rfl⟩ := h.p₀_surj g; exact h1 g
    · obtain ⟨g, rfl⟩ := h.p₀_surj g
      obtain ⟨g', rfl⟩ := h.p₀_surj g'
      simpa only [map_mul, map_inv] using h3 g g'
    · obtain ⟨g, rfl⟩ := h.p₀_surj g
      rw [← h.p₀_conj]; exact h4 g
    · rintro u _ ⟨g, hg, rfl⟩
      rw [← h.p₀_φu]; exact h5 u _ ⟨g, hg, rfl⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine ⟨fun g => h1 _, fun i j => (h.adicCont_iff _ fun g => z g i j).2 (h2 i j), fun g g' => ?_, fun g => ?_, ?_,
      fun v => (h6 v).imp fun Y hY => ⟨hY.1, (h.locAt_iff ρ w wi z v Y).2 hY.2⟩⟩
    · simpa only [map_mul, map_inv] using h3 (h.p₀ g) (h.p₀ g')
    · show z (h.p₀ (G.frame.conj g)) = _
      rw [h.p₀_conj]; exact h4 _
    · rintro u _ ⟨g, hg, rfl⟩
      show z (h.p₀ (G.φu u g)) = 0
      rw [h.p₀_φu]; exact h5 u _ ⟨g, hg, rfl⟩

theorem bd_iff : (fun g => z (h.p₀ g)) ∈ Bd G.frame (fun g => ρ (h.p₀ g)) V ↔ z ∈ Bd G'.frame ρ V := by
  refine exists_congr fun Y => and_congr_right fun _ => and_congr_right fun _ => ⟨fun e => funext fun g => ?_, ?_⟩
  · obtain ⟨g, rfl⟩ := h.p₀_surj g
    exact (congrFun e g).trans (h.dY_comp ρ Y g)
  · rintro rfl; exact funext fun g => (h.dY_comp ρ Y g).symm

end Sel

end Glob.Hom

namespace Lim

variable {G0 : Glob l L} {T : TWGrp G0} (Λ : Lim T)

abbrev Ph0 : Type := (Λ.G.η.comp Λ.πo).ker

theorem η_π (N : ℕ) (g : Λ.Ph) : (T.GN N).η (Λ.π N g) = Λ.G.η (Λ.πo g) := by
  have := T.H_η _ (Λ.modH N g)
  rw [map_mul, map_inv, mul_inv_eq_one, (T.h N).η, Λ.h.η] at this
  exact this

def π0 (N : ℕ) : Λ.Ph0 →* (T.GN N).G₀ :=
  ((Λ.π N).comp (Subgroup.subtype _)).codRestrict _ fun g => (Λ.η_π N g).trans g.2

def πo0 : Λ.Ph0 →* Λ.G.G₀ := (Λ.πo.comp (Subgroup.subtype _)).codRestrict _ fun g => g.2

@[simp] theorem coe_π0 (N : ℕ) (g : Λ.Ph0) : (Λ.π0 N g : (T.GN N).Γ) = Λ.π N g := rfl

@[simp] theorem coe_πo0 (g : Λ.Ph0) : (Λ.πo0 g : Λ.G.Γ) = Λ.πo g := rfl

theorem π0_cont (N : ℕ) : Continuous (Λ.π0 N) := ((Λ.π_cont N).comp continuous_subtype_val).subtype_mk _

theorem πo0_cont : Continuous Λ.πo0 := (Λ.πo_cont.comp continuous_subtype_val).subtype_mk _

theorem π0_surj (N : ℕ) : Function.Surjective (Λ.π0 N) := fun g => by
  obtain ⟨a, ha⟩ := Λ.π_surj N g
  exact ⟨⟨a, (Λ.η_π N a).symm.trans (by rw [ha]; exact g.2)⟩, Subtype.ext ha⟩

theorem πo0_surj : Function.Surjective Λ.πo0 := fun g => by
  obtain ⟨a, ha⟩ := Λ.πo_surj g
  exact ⟨⟨a, show Λ.G.η (Λ.πo a) = 1 by rw [ha]; exact g.2⟩, Subtype.ext ha⟩

theorem Ph0_open : IsOpen ((Λ.G.η.comp Λ.πo).ker : Set Λ.Ph) := Λ.G.η_open.preimage Λ.πo_cont

instance : CompactSpace Λ.Ph0 := isCompact_iff_compactSpace.1 (Subgroup.isClosed_of_isOpen _ Λ.Ph0_open).isCompact

def Rel (N : ℕ) {Z : Type} (zN : (T.GN N).G₀ → Z) (z : Λ.G.G₀ → Z) : Prop := ∀ g, zN (Λ.π0 N g) = z (Λ.πo0 g)

end Lim

section Fin

variable {G G0 : Glob l L} (h : G.Hom G0) {n : ℕ} {x : NP G0.frame n} (k : Kap x)

def FirstSelmerCardBoundAtAllLevels (D0 : ℕ) : Prop :=
  ∃ C : ℕ, ∀ m, (Sel1 h (x.Am m) k).Finite ∧
    (Sel1 h (x.Am m) k).ncard ≤ (Bd1 h (x.Am m) k).ncard * Nat.card x.K ^ (m * D0 + C)

def SecondSelmerSpanBoundAtAllLevels : Prop :=
  ∃ C : ℕ, ∀ m, ∀ z : Fin (k.g + 1) → Fin k.g → G.G₀ → Matrix (Fin n) (Fin n) (x.Am m),
    (∀ i j, z i j ∈ SelP h x (x.Am m)) → ∃ c : Fin (k.g + 1) → x.A, (∃ i, IsUnit (c i)) ∧
      ∃ Ψ ∈ Sel2 h (x.Am m) k, ∀ j γ a b, (Ψ γ a b).ep' j = (x.t ^ C • ∑ i, c i • z i j γ) a b

end Fin

section Desc

variable {G G' : Glob l L} (g : G.Hom G') {n : ℕ} (x : NP G.frame n) (ρ' : G'.G₀ →* GL (Fin n) x.A)
  (hρ : ∀ a, ρ' (g.p₀ a) = x.ρ a)

@[reducible] def NP.desc : NP G'.frame n where
  K := x.K
  ρ := ρ'
  cont i j := (g.adicCont_iff _ fun a => mat ρ' a i j).1 (by
    have : (fun a => mat ρ' (g.p₀ a) i j) = fun a => mat x.ρ a i j := funext fun a => by simp only [mat, MonoidHom.comp_apply, hρ]
    rw [this]; exact x.cont i j)
  form a := by
    obtain ⟨a, rfl⟩ := g.p₀_surj a
    have := x.form a
    rw [← g.p₀_conj, g.eps_p₀]
    simpa only [mat, MonoidHom.comp_apply, hρ] using this
  a := x.a
  a_pos := x.a_pos
  a_le := x.a_le
  blk a := by
    obtain ⟨a, rfl⟩ := g.p₀_surj a
    simpa only [mat, MonoidHom.comp_apply, hρ] using x.blk a
  span Z hZ := (x.span Z hZ).imp fun s hs => Submodule.span_mono (by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨g.p₀ a, (g.p₀_mem_G' a).2 ha, by simp only [mat, MonoidHom.comp_apply, hρ]⟩) hs
  ine := by
    rintro u _ ⟨a, ha, rfl⟩
    rw [← g.p₀_φu, hρ]; exact x.ine u _ ⟨a, ha, rfl⟩
  ψ := x.ψ
  ψ_mu := x.ψ_mu
  w := x.w
  ty := x.ty
  w_blk := x.w_blk
  tri v a := by
    have e : ρ' (G'.frame.φ v a) = x.ρ (G.frame.φ v a) := by rw [← hρ]; exact congrArg ρ' (g.p₀_φ v a).symm
    rw [e]; exact x.tri v a
  N1 v := by
    have e : (G'.frame.eps ℤ_[l] (PowerSeries x.K)).comp (G'.frame.φ v) =
        (G.frame.eps ℤ_[l] (PowerSeries x.K)).comp (G.frame.φ v) := MonoidHom.ext fun a => by
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, ← g.eps_p₀]
      exact congrArg _ (g.p₀_φ v a).symm
    rw [e]; exact x.N1 v

theorem NP.desc_ρX (X : Type) [CommRing X] [Algebra x.A X] (a : G.G₀) :
    (x.desc g ρ' hρ).ρX X (g.p₀ a) = x.ρX X a := by
  show (mat ρ' (g.p₀ a)).map _ = (mat x.ρ a).map _
  simp only [mat, MonoidHom.comp_apply, hρ]

variable {x} (k : Kap x) (κ' : Fin k.g → G'.G₀ → Matrix (Fin n) (Fin n) x.A) (hκ : ∀ j a, κ' j (g.p₀ a) = k.κ j a)

@[reducible] def Kap.desc : Kap (x.desc g ρ' hρ) :=
  have e : (fun a => (x.desc g ρ' hρ).ρX x.A (g.p₀ a)) = x.ρX x.A := funext (x.desc_ρX g ρ' hρ x.A)
  have e' : ∀ j, (fun a => κ' j (g.p₀ a)) = k.κ j := fun j => funext (hκ j)
  { g := k.g
    κ := κ'
    mem := fun j => (g.sel_iff _ _ _ _ _ _).1 (by rw [e' j]; exact e ▸ k.mem j)
    Y := k.Y
    Y_mem := k.Y_mem
    loc := fun j v => (g.locAt_iff _ _ _ _ _ _).1 (by rw [e' j]; exact e ▸ k.loc j v)
    indep := fun c hc => k.indep c (by
      have := (g.bd_iff _ _ _).2 hc
      rw [e] at this
      convert this using 1
      funext a
      simp only [Finset.sum_apply, Pi.smul_apply, hκ])
    gen := fun z hz => by
      have h1 := (g.sel_iff _ _ _ _ _ _).2 hz
      rw [e] at h1
      obtain ⟨s, c, hc⟩ := k.gen _ h1
      refine ⟨s, c, (g.bd_iff _ _ _).1 ?_⟩
      rw [e]
      convert hc using 1
      funext a
      simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, hκ] }

end Desc

structure TWQuot {G0 : Glob l L} (T : TWGrp G0) : Type 1 where
  G0' : Glob l L
  g0 : G0.Hom G0'
  ker0 : g0.p.ker = PL l T.H.toSubgroup
  GN' : ℕ → Glob l L
  gN : ∀ N, (T.GN N).Hom (GN' N)
  kerN : ∀ N, (gN N).p.ker = PL l (T.H.toSubgroup.comap (T.h N).p)
  h' : ∀ N, (GN' N).Hom G0'
  comm : ∀ N a, (h' N).p ((gN N).p a) = g0.p ((T.h N).p a)
  H' : OpenNormalSubgroup G0'.Γ
  H'_iff : ∀ a, g0.p a ∈ H' ↔ a ∈ T.H
  ph_lim : ∀ (V : OpenNormalSubgroup G0'.Γ) j, ∀ᶠ N in atTop, g0.p ((T.h N).p (T.ph N j) * (T.sg j : G0.Γ)⁻¹) ∈ V
  ker_le : ∀ N, (h' N).p.ker ≤ (Subgroup.normalClosure (Set.range fun j => (gN N).p (T.ta N j))).topologicalClosure
  fin0 : Finite (HomL l H'.toSubgroup)
  finN : ∀ N, Finite (HomL l (H'.toSubgroup.comap (h' N).p)) ∧ Nat.card (HomL l (H'.toSubgroup.comap (h' N).p)) ≤ T.hb
  pl0 : PL l H'.toSubgroup = ⊥
  plN : ∀ N, PL l (H'.toSubgroup.comap (h' N).p) = ⊥

namespace TWQuot

variable {G0 : Glob l L} {T : TWGrp G0} (Q : TWQuot T)

theorem comm₀ (N : ℕ) (a : (T.GN N).G₀) : (Q.h' N).p₀ ((Q.gN N).p₀ a) = Q.g0.p₀ ((T.h N).p₀ a) :=
  Subtype.ext (Q.comm N a)

@[reducible] def grp : TWGrp Q.G0' where
  q := T.q
  H := Q.H'
  H_η a ha := by
    obtain ⟨a, rfl⟩ := Q.g0.surj a
    rw [Q.g0.η]; exact T.H_η a ((Q.H'_iff a).1 ha)
  H_ε a ha := by
    obtain ⟨a, rfl⟩ := Q.g0.surj a
    rw [Q.g0.ε]; exact T.H_ε a ((Q.H'_iff a).1 ha)
  GN := Q.GN'
  h := Q.h'
  sg j := Q.g0.p₀ (T.sg j)
  sg_mem j := (Q.g0.p₀_mem_G' _).2 (T.sg_mem j)
  Nq := T.Nq
  Nq_mod := T.Nq_mod
  ph N j := (Q.gN N).p₀ (T.ph N j)
  ta N j := (Q.gN N).p₀ (T.ta N j)
  ph_lim V j _ := (Q.ph_lim V j).mono fun N hN => by
    simpa only [map_mul, map_inv, Glob.Hom.coe_p₀, Q.comm] using hN
  ph_H N j := by
    have := (Q.H'_iff _).2 (T.ph_H N j)
    simpa only [map_mul, map_inv, Glob.Hom.coe_p₀, Q.comm] using this
  ta_ker N j := by rw [Glob.Hom.coe_p₀, Q.comm, T.ta_ker, map_one]
  tame N j := by
    have := T.tame N j
    rw [← Q.kerN, MonoidHom.mem_ker] at this
    have e : ((((Q.gN N).p₀ (T.ta N j) ^ T.Nq N j)⁻¹ * (((Q.gN N).p₀ (T.ph N j))⁻¹ * (Q.gN N).p₀ (T.ta N j) *
        (Q.gN N).p₀ (T.ph N j)) : (Q.GN' N).G₀) : (Q.GN' N).Γ) = 1 := by
      rw [← this, ← Glob.Hom.coe_p₀]
      simp only [map_mul, map_inv, map_pow]
    rw [e]; exact one_mem _
  ker_le N := (Q.ker_le N).trans (Subgroup.topologicalClosure_mono le_sup_left)
  hb := T.hb
  fin0 := Q.fin0
  finN := Q.finN
  phiV := T.phiV
  phiU := T.phiU

theorem proL : Q.grp.ProL := ⟨Q.pl0, Q.plN⟩

end TWQuot

end UpperTheory.V.Pa
