import ReciprocityTheory.GroupCohomology.CupConnRightStatement
import ReciprocityTheory.GroupCohomology.DEqZeroOfMemB
import ReciprocityTheory.GroupCohomology.LowHolds
import ReciprocityTheory.GroupCohomology.InnerHolds

namespace ReciprocityTheory.Coh.InflationRestrictionInvariants

open ReciprocityTheory.Gal Cx Function

universe u

noncomputable section

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

instance instCCSInv (M : TRep R G) (N : Subgroup G) :
    ContinuousConstSMul R (Representation.invariants (M.rho.comp N.subtype)) :=
  ⟨fun c => (continuous_subtype_val.const_smul c).subtype_mk _⟩

abbrev invQ (M : TRep R G) (N : Subgroup G) [N.Normal] : TRep R (G ⧸ N) where
  V := Representation.invariants (M.rho.comp N.subtype)
  rho := Representation.quotientToInvariants M.rho N
  cont := by
    have hq : Topology.IsQuotientMap (fun p : G × Representation.invariants (M.rho.comp N.subtype) =>
        ((p.1 : G ⧸ N), p.2)) :=
      (QuotientGroup.isOpenQuotientMap_mk.prodMap IsOpenQuotientMap.id).isQuotientMap
    unfold Gal.ContAction
    rw [hq.continuous_iff]
    refine Continuous.subtype_mk ?_ _
    exact M.cont.comp ((continuous_fst).prodMk (continuous_subtype_val.comp continuous_snd))

def invP (M : TRep R G) (N : Subgroup G) [N.Normal] : Pair (invQ M N) M where
  φ := QuotientGroup.mk' N
  u := (Representation.invariants (M.rho.comp N.subtype)).subtype
  φ_cont := continuous_quot_mk
  u_cont := continuous_subtype_val
  equiv _ _ := rfl

theorem invariants_isInvRep (M : TRep R G) (N : Subgroup G) [N.Normal] : IsInvRep M N (invQ M N) (invP M N) := by
  refine ⟨rfl, Topology.IsEmbedding.subtypeVal, fun m => ?_⟩
  constructor
  · rintro ⟨v, rfl⟩ g hg
    exact v.2 ⟨g, hg⟩
  · intro h
    exact ⟨⟨m, fun g => h g.1 g.2⟩, rfl⟩

end

end ReciprocityTheory.Coh.InflationRestrictionInvariants

namespace ReciprocityTheory.Coh.InflationRestrictionInvariants

open ReciprocityTheory.Gal Cx Function

universe u

noncomputable section

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

abbrev e1 (a : G) : Fin 1 → G := fun _ => a

theorem oneCochain_apply_fin_one (M : TRep R G) (x : M.coch.X 1) (g : Fin 1 → G) : x.1 g = x.1 (e1 (g 0)) :=
  congrArg x.1 (funext fun i => by rw [Fin.fin_one_eq_zero i])

theorem memZ {A : Cx R} {n : ℕ} (x : A.X n) : x ∈ A.Z n ↔ A.d n x = 0 := LinearMap.mem_ker

theorem memB {A : Cx R} {n : ℕ} (x : A.X (n + 1)) : x ∈ A.B (n + 1) ↔ ∃ y, A.d n y = x :=
  LinearMap.mem_range

theorem H_mk {A B : Cx R} (φ : Hom A B) (n : ℕ) (z : A.Z n) :
    φ.H n (Submodule.Quotient.mk z) = Submodule.Quotient.mk (φ.Z n z) := rfl

theorem mk_eq_zero_iff {A : Cx R} {n : ℕ} (z : A.Z n) :
    (Submodule.Quotient.mk z : A.H n) = 0 ↔ z.1 ∈ A.B n := by
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  rfl

theorem oneDifferential_val (M : TRep R G) (x : M.coch.X 1) (a b : G) :
    (M.coch.d 1 x).1 ![a, b] = M.rho a (x.1 (e1 b)) - x.1 (e1 (a * b)) + x.1 (e1 a) := by
  show ReciprocityTheory.Gal.dn M.rho 1 x.1 ![a, b] = _
  rw [LowDeg.dn_one_apply]
  have he : ∀ c : G, (![c] : Fin 1 → G) = e1 c := fun c => funext fun i => by
    rw [Fin.fin_one_eq_zero i]; rfl
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, he]

theorem wach_d1_eq_zero_iff (M : TRep R G) (x : M.coch.X 1) :
    M.coch.d 1 x = 0 ↔ ∀ a b, x.1 (e1 (a * b)) = x.1 (e1 a) + M.rho a (x.1 (e1 b)) := by
  constructor
  · intro h a b
    have h1 := congrArg (fun y : M.coch.X 2 => y.1 ![a, b]) h
    simp only [oneDifferential_val] at h1
    have h2 : (0 : M.coch.X 2).1 ![a, b] = 0 := rfl
    rw [h2] at h1
    rw [← sub_eq_zero, show x.1 (e1 (a * b)) - (x.1 (e1 a) + M.rho a (x.1 (e1 b))) =
      -(M.rho a (x.1 (e1 b)) - x.1 (e1 (a * b)) + x.1 (e1 a)) by abel, h1, neg_zero]
  · intro h
    apply Subtype.ext
    funext v
    have hv : v = ![v 0, v 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hv, oneDifferential_val, h]
    show _ = (0 : M.V)
    abel

theorem zeroDifferential_val (M : TRep R G) (y : M.coch.X 0) (a : G) :
    (M.coch.d 0 y).1 (e1 a) = M.rho a (y.1 ![]) - y.1 ![] := by
  show ReciprocityTheory.Gal.dn M.rho 0 y.1 (e1 a) = _
  rw [LowDeg.dn_zero_apply]

def const0 (M : TRep R G) (m : M.V) : M.coch.X 0 := ⟨fun _ => m, continuous_const⟩

theorem mem_oneCoboundaries_iff (M : TRep R G) (x : M.coch.X 1) :
    x ∈ M.coch.B 1 ↔ ∃ m, ∀ a, x.1 (e1 a) = M.rho a m - m := by
  rw [memB]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y.1 ![], fun a => zeroDifferential_val M y a⟩
  · rintro ⟨m, hm⟩
    refine ⟨const0 M m, Subtype.ext (funext fun g => ?_)⟩
    rw [oneCochain_apply_fin_one M x g, hm, oneCochain_apply_fin_one M (M.coch.d 0 (const0 M m)) g, zeroDifferential_val]
    rfl

end

end ReciprocityTheory.Coh.InflationRestrictionInvariants

namespace ReciprocityTheory.Coh.InflationRestrictionInvariants

open ReciprocityTheory.Gal Cx Function

universe u

noncomputable section

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem cocycle_one (M : TRep R G) (x : M.coch.X 1) (hx : M.coch.d 1 x = 0) : x.1 (e1 1) = 0 := by
  have h := (wach_d1_eq_zero_iff M x).mp hx 1 1
  rw [mul_one, map_one, Module.End.one_apply] at h
  have h2 : x.1 (e1 1) + x.1 (e1 1) - x.1 (e1 1) = 0 := by rw [← h]; abel
  simpa using h2

theorem inf_inj (M : TRep R G) (N : Subgroup G) [N.Normal] (Q : TRep R (G ⧸ N)) (P : Pair Q M)
    (hP : IsInvRep M N Q P) : Injective (P.hom.H 1) := by
  obtain ⟨hφ, hemb, hrg⟩ := hP
  have hφa : ∀ a, P.φ a = (a : G ⧸ N) := fun a => by rw [hφ]; rfl
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro h hh
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ h
  rw [H_mk, mk_eq_zero_iff, mem_oneCoboundaries_iff] at hh
  obtain ⟨m, hm⟩ := hh
  have hm' : ∀ a, P.u (z.1.1 (e1 (P.φ a))) = M.rho a m - m := hm
  have hz1 := cocycle_one Q z.1 ((memZ _).1 z.2)
  have hmN : ∀ g ∈ N, M.rho g m = m := fun g hg => by
    have := hm' g
    rw [hφa, (QuotientGroup.eq_one_iff g).2 hg, hz1, map_zero] at this
    exact (sub_eq_zero.1 this.symm)
  obtain ⟨q, rfl⟩ := (hrg m).2 hmN
  rw [mk_eq_zero_iff, mem_oneCoboundaries_iff]
  refine ⟨q, fun γ => ?_⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective γ
  apply hemb.injective
  rw [← hφa, hm' a, map_sub, P.equiv]

theorem inf_res_exact (M : TRep R G) (N : Subgroup G) [N.Normal] (Q : TRep R (G ⧸ N)) (P : Pair Q M)
    (hP : IsInvRep M N Q P) :
    Exact (P.hom.H 1) ((Pair.res M N.subtype continuous_subtype_val).hom.H 1) := by
  obtain ⟨hφ, hemb, hrg⟩ := hP
  have hφa : ∀ a, P.φ a = (a : G ⧸ N) := fun a => by rw [hφ]; rfl
  intro y
  constructor
  · intro hy
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [H_mk, mk_eq_zero_iff, mem_oneCoboundaries_iff] at hy
    obtain ⟨m0, hm0⟩ := hy
    obtain ⟨m, hm'⟩ : ∃ m : M.V, ∀ n : N, z.1.1 (e1 (n : G)) = M.rho n m - m := ⟨m0, hm0⟩
    obtain ⟨x', hx'⟩ : ∃ x' : M.coch.X 1, x' = z.1 - M.coch.d 0 (const0 M m) := ⟨_, rfl⟩
    have hx'v : ∀ a, x'.1 (e1 a) = z.1.1 (e1 a) - (M.rho a m - m) := fun a => by
      rw [hx']
      show z.1.1 (e1 a) - (M.coch.d 0 (const0 M m)).1 (e1 a) = _
      rw [zeroDifferential_val]; rfl
    have hx'c : M.coch.d 1 x' = 0 := by
      rw [hx', map_sub, (memZ _).1 z.2, M.coch.dd, sub_zero]
    have hcoc := (wach_d1_eq_zero_iff M x').1 hx'c
    have hN : ∀ n ∈ N, x'.1 (e1 n) = 0 := fun n hn => by rw [hx'v, hm' ⟨n, hn⟩, sub_self]
    have hconst : ∀ a n, n ∈ N → x'.1 (e1 (a * n)) = x'.1 (e1 a) := fun a n hn => by
      rw [hcoc, hN n hn, map_zero, add_zero]
    have hinv : ∀ a, ∀ n ∈ N, M.rho n (x'.1 (e1 a)) = x'.1 (e1 a) := fun a n hn => by
      have h1 := hcoc n a
      rw [hN n hn, zero_add] at h1
      rw [← h1]
      have : n * a = a * (a⁻¹ * n * a) := by group
      rw [this, hconst a _ (Subgroup.Normal.conj_mem' ‹_› n hn a)]
    have hmem : ∀ a, ∃ q, P.u q = x'.1 (e1 a) := fun a => (hrg _).2 (hinv a)
    choose F0 hF0 using hmem
    have hF0c : ∀ a b : G, (a : G ⧸ N) = b → F0 a = F0 b := fun a b hab => hemb.injective (by
      have hb : b = a * (a⁻¹ * b) := by group
      rw [hF0, hF0, hb, hconst a _ (QuotientGroup.eq.1 hab)])
    let F : G ⧸ N → Q.V := fun γ => F0 γ.out
    have hF : ∀ a : G, F a = F0 a := fun a => hF0c _ _ (QuotientGroup.out_eq' _)
    have hFc : Continuous F := by
      rw [hemb.continuous_iff, (QuotientGroup.isQuotientMap_mk N).continuous_iff]
      have : (P.u ∘ F) ∘ (QuotientGroup.mk : G → G ⧸ N) = fun a => x'.1 (e1 a) :=
        funext fun a => by simp only [comp_apply, hF, hF0]
      rw [this]
      exact (show Continuous x'.1 from x'.2).comp (continuous_pi fun _ => continuous_id)
    let w : Q.coch.X 1 := ⟨fun g => F (g 0), hFc.comp (continuous_apply 0)⟩
    have hw : Q.coch.d 1 w = 0 := by
      rw [wach_d1_eq_zero_iff]
      intro γ δ
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective γ
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective δ
      apply hemb.injective
      show P.u (F (↑a * ↑b)) = P.u (F ↑a + Q.rho ↑a (F ↑b))
      rw [← QuotientGroup.mk_mul, hF, hF, hF, map_add, ← hφa, P.equiv, hF0, hF0, hF0, hcoc]
    refine ⟨Submodule.Quotient.mk ⟨w, (memZ _).2 hw⟩, ?_⟩
    rw [H_mk, Submodule.Quotient.eq, Submodule.mem_comap]
    have hwx : P.hom.f 1 w = x' := Subtype.ext (funext fun g => by
      rw [oneCochain_apply_fin_one M _ g, oneCochain_apply_fin_one M x' g]
      show P.u (F (P.φ (g 0))) = x'.1 (e1 (g 0))
      rw [hφa, hF, hF0])
    show P.hom.f 1 w - z.1 ∈ M.coch.B 1
    rw [hwx, hx', memB]
    exact ⟨-const0 M m, by rw [map_neg]; abel⟩
  · rintro ⟨y0, rfl⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y0
    rw [H_mk, H_mk, mk_eq_zero_iff]
    have h0 : ((Pair.res M N.subtype continuous_subtype_val).hom.Z 1 (P.hom.Z 1 z)).1 = 0 :=
      Subtype.ext (funext fun g => by
        show P.u (z.1.1 (fun i => P.φ (g i).1)) = 0
        have : (fun i => P.φ (g i).1) = e1 1 :=
          funext fun i => by rw [hφa, (QuotientGroup.eq_one_iff _).2 (g i).2]
        rw [this, cocycle_one Q z.1 ((memZ _).1 z.2), map_zero])
    rw [h0]
    exact Submodule.zero_mem _

def conjPair (M : TRep R G) (s : G) : Pair M M where
  φ := { toFun := fun g => s⁻¹ * g * s, map_one' := by group, map_mul' := fun a b => by group }
  u := M.rho s
  φ_cont := (continuous_const.mul continuous_id).mul continuous_const
  u_cont := M.cont.comp (continuous_const.prodMk continuous_id)
  equiv g m := by
    show (M.rho s * M.rho (s⁻¹ * g * s)) m = (M.rho g * M.rho s) m
    rw [← map_mul, ← map_mul]
    congr 2
    group

theorem conj_res (M : TRep R G) (N : Subgroup G) (s : G) (c : Pair (M.resSub N) (M.resSub N))
    (hc : ∀ g, (c.φ g : G) = s⁻¹ * g * s) (hu : ∀ m, c.u m = M.rho s m) (n : ℕ) (x : M.H n) :
    c.hom.H n ((Pair.res M N.subtype continuous_subtype_val).hom.H n x) =
      (Pair.res M N.subtype continuous_subtype_val).hom.H n x := by
  have hinner := inner_holds R G M (conjPair M s) s (fun g => rfl) (fun m => rfl) n
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  calc c.hom.H n ((Pair.res M N.subtype continuous_subtype_val).hom.H n (Submodule.Quotient.mk z))
      = (Pair.res M N.subtype continuous_subtype_val).hom.H n
          ((conjPair M s).hom.H n (Submodule.Quotient.mk z)) := by
        rw [H_mk, H_mk, H_mk, H_mk]
        congr 1
        apply Subtype.ext; apply Subtype.ext; funext g
        show c.u (z.1.1 fun i => ((c.φ (g i)) : G)) = M.rho s (z.1.1 fun i => s⁻¹ * (g i : G) * s)
        simp only [hc]; exact hu _
    _ = _ := by rw [hinner, LinearMap.id_apply]

end

end ReciprocityTheory.Coh.InflationRestrictionInvariants

namespace ReciprocityTheory.Coh

open InflationRestrictionInvariants

universe u

theorem invRep_holds : InvRepStatement.{u} := fun R _ G _ _ _ M N _ =>
  ⟨invQ M N, invP M N, invariants_isInvRep M N⟩

theorem infRes_holds : InfResStatement.{u} := fun R _ G _ _ _ M N _ Q P hP =>
  ⟨inf_inj M N Q P hP, inf_res_exact M N Q P hP, fun s c h1 h2 n x => conj_res M N s c h1 h2 n x⟩

end ReciprocityTheory.Coh
