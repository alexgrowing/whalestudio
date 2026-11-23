import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.LSigFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTateSimilitudeHeckeTranslateGeometric

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.G3 (sp)
open UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.lPts_holds :
    LGrp → LPts := by
  intro hLG E _ Γ _ X O _ _ K K₀ K₁ KN M N Y Y' pY π π' s a b hKN hNK hN0 h10 hπ hQ0 hQ1 hcomm
    hcov b₀ hb₀ Ω _ _ z y' hy'
  subst hKN
  have hMN : X.K M ≤ X.K N := fun v hv => by simpa using b v hv
  have hM1 : X.K M ≤ K₁ := hQ1.le
  have ad := hQ0.adm
  have hnorm : ∀ g ∈ K₀, ∀ v ∈ X.K M, g * v * g⁻¹ ∈ X.K M := fun g hg => (ad g hg).2
  have trc : ∀ g g' (e : g = g') a b a' b', X.tr M M g a b = X.tr M M g' a' b' := by
    intro g g' e a b a' b'
    subst e
    rfl
  have trm : ∀ g g' (hg : g ∈ K₀) (hg' : g' ∈ K₀) a b a' b',
      X.tr M M g a b ≫ X.tr M M g' a' b' =
        X.tr M M (g' * g) (ad _ (K₀.mul_mem hg' hg)).1 (ad _ (K₀.mul_mem hg' hg)).2 :=
    fun g g' hg hg' a b a' b' => X.tr_mul _ _ _ _ _ _ _ _ _ _ _
  haveI := X.onto M N a b
  haveI := X.fin M N a b
  haveI := X.etale M N a b
  obtain ⟨x₀, hx₀⟩ := GlobalTheory.GeomSurj.exists_lift_of_surjective (X.tr M N 1 a b) z
  obtain ⟨x₁, hx₁⟩ := hQ1.onto Ω y' (z ≫ X.q N)
    (by rw [← Category.assoc, hy', Category.assoc, hπ, ← Category.assoc])
  obtain ⟨u, hu, au, bu, hx₁u⟩ := hQ0.fib Ω x₀ x₁ (by
    have e1 : x₀ ≫ π' ≫ s = z ≫ π := by rw [← hcomm, ← Category.assoc, ← hx₀]
    have e2 : x₁ ≫ π' ≫ s = z ≫ π := by rw [← Category.assoc, hx₁, hy']
    rw [e1, e2])
  have cond : ∀ h (hh : h ∈ K₀) a' b', x₀ ≫ X.tr M M h a' b' ≫ π' = y' ↔ h * u⁻¹ ∈ K₁ := by
    intro h hh a' b'
    constructor
    · intro hy
      have e : x₀ ≫ X.tr M M u au bu ≫ π' = x₀ ≫ X.tr M M h a' b' ≫ π' := by
        rw [hy, ← hx₁, hx₁u, Category.assoc]
      obtain ⟨w, hw, aw, bw, hw'⟩ := hQ1.fib Ω (x₀ ≫ X.tr M M u au bu) (x₀ ≫ X.tr M M h a' b')
        (by simpa only [Category.assoc] using e)
      have hwu : w * u ∈ K₀ := K₀.mul_mem (h10 hw) hu
      have e2 : x₀ ≫ X.tr M M h a' b' = x₀ ≫ X.tr M M (w * u) (ad _ hwu).1 (ad _ hwu).2 := by
        rw [hw', Category.assoc, trm _ _ hu (h10 hw)]
      have hk : h * (w * u)⁻¹ ∈ K₀ := K₀.mul_mem hh (K₀.inv_mem hwu)
      have e3 : (x₀ ≫ X.tr M M (w * u) (ad _ hwu).1 (ad _ hwu).2) ≫
          X.tr M M (h * (w * u)⁻¹) (ad _ hk).1 (ad _ hk).2 =
            x₀ ≫ X.tr M M (w * u) (ad _ hwu).1 (ad _ hwu).2 := by
        rw [Category.assoc, trm _ _ hwu hk, ← e2]
        congr 1
        exact trc _ _ (by group) _ _ _ _
      have hin := hQ0.free _ hk _ _ Ω _ e3
      have h2 : h * u⁻¹ = (h * (w * u)⁻¹) * w := by group
      rw [h2]
      exact K₁.mul_mem (hM1 hin) hw
    · intro hw
      have hw0 : h * u⁻¹ ∈ K₀ := h10 hw
      have e : X.tr M M u au bu ≫ X.tr M M (h * u⁻¹) (ad _ hw0).1 (ad _ hw0).2 ≫ π' =
          X.tr M M h a' b' ≫ π' := by
        rw [← Category.assoc, trm _ _ hu hw0]
        congr 1
        exact trc _ _ (by group) _ _ _ _
      rw [hQ1.inv _ hw] at e
      rw [← hx₁, hx₁u, Category.assoc, e]
  have trg : ∀ i j (g g' : Γ) (e : g = g') a b a' b', X.tr i j g a b = X.tr i j g' a' b' := by
    intro i j g g' e a b a' b'
    subst e
    rfl
  have fibk : ∀ k ∈ X.K N, ∀ a' b', X.tr M M k a' b' ≫ X.tr M N 1 a b = X.tr M N 1 a b := by
    intro k hk a' b'
    have ak : k ∈ X.Δ := X.K_le N k hk
    have bk : ∀ v ∈ X.K N, k * v * k⁻¹ ∈ X.K N := fun v hv =>
      (X.K N).mul_mem ((X.K N).mul_mem hk hv) ((X.K N).inv_mem hk)
    have a1 : 1 * k ∈ X.Δ := by simpa using ak
    have b1 : ∀ v ∈ X.K M, 1 * k * v * (1 * k)⁻¹ ∈ X.K N := fun v hv =>
      hMN (by simpa using hnorm k (hN0 hk) v hv)
    have a2 : k * 1 ∈ X.Δ := by simpa using ak
    have b2 : ∀ v ∈ X.K M, k * 1 * v * (k * 1)⁻¹ ∈ X.K N := fun v hv =>
      hMN (by simpa using hnorm k (hN0 hk) v hv)
    rw [X.tr_mul M M N k 1 a' b' a b a1 b1, trg M N _ _ (by group) a1 b1 a2 b2,
      ← X.tr_mul M N N 1 k a b ak bk a2 b2, X.tr_self N k ak bk hk, Category.comp_id]
  have kN : ∀ n : ↥(X.K N) ⧸ (X.K M).subgroupOf (X.K N), ((Quotient.out n : X.K N) : Γ) ∈ K₀ :=
    fun n => hN0 (Quotient.out n).2
  obtain ⟨φ, hφdef⟩ : ∃ φ : (↥(X.K N) ⧸ (X.K M).subgroupOf (X.K N)) → (sp Ω ⟶ X.Z M),
      ∀ n, φ n = x₀ ≫ X.tr M M ((Quotient.out n : X.K N) : Γ) (ad _ (kN n)).1 (ad _ (kN n)).2 :=
    ⟨_, fun n => rfl⟩
  have hF : ∀ (c : ↥K ⧸ (X.K N).subgroupOf K) (n : ↥(X.K N) ⧸ (X.K M).subgroupOf (X.K N)),
      b₀⁻¹ * ↑(Quotient.out c) * ↑(Quotient.out n) * u⁻¹ ∈ K₁ →
      φ n ≫ X.tr M N 1 a b = z ∧ b₀⁻¹ * ↑(Quotient.out c) ∈ K₀ ∧
        ∀ (a' : b₀⁻¹ * ↑(Quotient.out c) ∈ X.Δ)
          (b' : ∀ v ∈ X.K M, b₀⁻¹ * ↑(Quotient.out c) * v * (b₀⁻¹ * ↑(Quotient.out c))⁻¹ ∈ X.K M),
          φ n ≫ X.tr M M (b₀⁻¹ * ↑(Quotient.out c)) a' b' ≫ π' = y' := by
    intro c n hcn
    have hn0 := kN n
    have hg : b₀⁻¹ * ↑(Quotient.out c) ∈ K₀ := by
      have e : b₀⁻¹ * ↑(Quotient.out c) = (b₀⁻¹ * ↑(Quotient.out c) * ↑(Quotient.out n) * u⁻¹) * u *
          (↑(Quotient.out n))⁻¹ := by group
      rw [e]
      exact K₀.mul_mem (K₀.mul_mem (h10 hcn) hu) (K₀.inv_mem hn0)
    refine ⟨?_, hg, fun a' b' => ?_⟩
    · rw [hφdef, Category.assoc, fibk _ (Quotient.out n).2, hx₀]
    · rw [hφdef, Category.assoc, ← Category.assoc (X.tr M M _ _ _), trm _ _ hn0 hg]
      exact (cond _ (K₀.mul_mem hg hn0) _ _).2 hcn
  rw [← hLG Γ K K₀ K₁ (X.K N) (X.K M) hMN hNK hN0 hM1 h10 hnorm hcov b₀ hb₀ u hu]
  symm
  apply Nat.card_congr
  refine Equiv.ofBijective (fun cn => ⟨(cn.1.1, φ cn.1.2), hF cn.1.1 cn.1.2 cn.2⟩) ⟨?_, ?_⟩
  · rintro ⟨⟨c1, n1⟩, h1⟩ ⟨⟨c2, n2⟩, h2⟩ hE
    have hc : c1 = c2 := congrArg (fun t => t.1.1) hE
    have hx : φ n1 = φ n2 := congrArg (fun t => t.1.2) hE
    subst hc
    have hn : n1 = n2 := by
      have hk1 := kN n1
      have hk2 := kN n2
      have hd : ((Quotient.out n2 : X.K N) : Γ) * ((Quotient.out n1 : X.K N) : Γ)⁻¹ ∈ K₀ :=
        K₀.mul_mem hk2 (K₀.inv_mem hk1)
      have e3 : φ n1 ≫ X.tr M M _ (ad _ hd).1 (ad _ hd).2 = φ n1 := by
        conv_rhs => rw [hx]
        rw [hφdef, hφdef, Category.assoc, trm _ _ hk1 hd]
        congr 1
        exact trc _ _ (by group) _ _ _ _
      have hdM := hQ0.free _ hd _ _ Ω _ e3
      rw [← QuotientGroup.out_eq' n1, ← QuotientGroup.out_eq' n2, QuotientGroup.eq,
        Subgroup.mem_subgroupOf]
      have e4 : (((Quotient.out n1)⁻¹ * Quotient.out n2 : X.K N) : Γ) =
          ((Quotient.out n1 : X.K N) : Γ)⁻¹ *
            (((Quotient.out n2 : X.K N) : Γ) * ((Quotient.out n1 : X.K N) : Γ)⁻¹) *
              ((Quotient.out n1 : X.K N) : Γ)⁻¹⁻¹ := by
        push_cast
        group
      rw [e4]
      exact hnorm _ (K₀.inv_mem hk1) _ hdM
    subst hn
    rfl
  · rintro ⟨⟨c, x⟩, hx, hg, hy⟩
    dsimp only at hx hg hy
    obtain ⟨k, hk, ak, bk, hxk⟩ := X.trans M N a b (fun k hk v hv => hnorm k (hN0 hk) v hv) Ω x₀ x
      (by rw [hx, hx₀])
    obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul ((X.K M).subgroupOf (X.K N)) (⟨k, hk⟩ : X.K N)
    have hφ : φ (QuotientGroup.mk ⟨k, hk⟩) = x := by
      rw [hxk, hφdef]
      have hmM : ((m : X.K N) : Γ) ∈ X.K M := Subgroup.mem_subgroupOf.mp m.2
      have hmK0 : ((m : X.K N) : Γ) ∈ K₀ := hN0 (hMN hmM)
      have e : ((Quotient.out (QuotientGroup.mk ⟨k, hk⟩ : ↥(X.K N) ⧸ (X.K M).subgroupOf (X.K N)) :
          X.K N) : Γ) = k * ((m : X.K N) : Γ) := by
        rw [hm]
        rfl
      congr 1
      rw [trc _ _ e _ _ (ad _ (K₀.mul_mem (hN0 hk) hmK0)).1 (ad _ (K₀.mul_mem (hN0 hk) hmK0)).2,
        ← trm _ _ hmK0 (hN0 hk) (ad _ hmK0).1 (ad _ hmK0).2 ak bk, X.tr_self M _ _ _ hmM,
        Category.id_comp]
    have hn0 := kN (QuotientGroup.mk ⟨k, hk⟩ : ↥(X.K N) ⧸ (X.K M).subgroupOf (X.K N))
    have hyy := hy (ad _ hg).1 (ad _ hg).2
    rw [← hφ, hφdef] at hyy
    have hmem := (cond _ (K₀.mul_mem hg hn0) (ad _ (K₀.mul_mem hg hn0)).1
      (ad _ (K₀.mul_mem hg hn0)).2).1 (by
        rw [← trm _ _ hn0 hg]
        simpa only [Category.assoc] using hyy)
    refine ⟨⟨(c, QuotientGroup.mk ⟨k, hk⟩), hmem⟩, ?_⟩
    apply Subtype.ext
    exact Prod.ext rfl hφ
